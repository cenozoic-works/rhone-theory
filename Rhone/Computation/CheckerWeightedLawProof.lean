/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerOrderedCountsProof

/-! # Multinomially weighted sampling law -/

@[expose] public section
namespace Rhone.Computation.CheckerSpec

open Finset LinearAlgebra.Recursion Coalescent.TwoLocusGenealogy Probability.InfiniteAlleles

noncomputable def fullyTyped (n : Nat) : Finset (Config 2 2) := by
  classical
  exact univ.image fun p : (Fin n → Fin 2) × (Fin n → Fin 2) => cSample p.1 p.2

theorem cSample_total {n : Nat} (a b : Fin n → Fin 2) : (cSample a b).t = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n)))
    (t := (univ : Finset (Fin 2 × Fin 2))) (f := fun k => (a k, b k))
    (fun _ _ => mem_univ _)
  simpa [Config.t, cSample, Fintype.sum_prod_type, Prod.mk.injEq] using h.symm

theorem mem_fullyTyped {n : Nat} {ξ : Config 2 2} :
    ξ ∈ fullyTyped n ↔ ξ.a = (fun _ => 0) ∧ ξ.b = (fun _ => 0) ∧ ξ.t = n := by
  classical
  constructor
  · intro h
    obtain ⟨p, _, rfl⟩ := mem_image.mp h
    exact ⟨rfl, rfl, cSample_total p.1 p.2⟩
  · rintro ⟨ha, hb, ht⟩
    let counts := fun cell : Fin 2 × Fin 2 => ξ.c cell.1 cell.2
    have htotal : ∑ cell, counts cell = n := by
      rw [Fintype.sum_prod_type]
      exact ht
    obtain ⟨f, hf⟩ := exists_fibreCard counts htotal
    apply mem_image.mpr
    refine ⟨(fun k => (f k).1, fun k => (f k).2), mem_univ _, ?_⟩
    apply (cSample_eq_iff _ _ ξ ha hb).mpr
    simpa only [Prod.eta] using hf

theorem card_orderedProfile_rat {n : Nat} {ξ : Config 2 2} (h : ξ ∈ fullyTyped n) :
    ((orderedProfile n ξ).card : Rat) =
      (Nat.factorial n : Rat) / ((∏ i, ∏ j, Nat.factorial (ξ.c i j) : Nat) : Rat) := by
  classical
  obtain ⟨ha, hb, ht⟩ := mem_fullyTyped.mp h
  have hden : (((∏ i, ∏ j, Nat.factorial (ξ.c i j)) : Nat) : Rat) ≠ 0 := by
    simp [Nat.factorial_ne_zero]
  apply (eq_div_iff hden).mpr
  exact_mod_cast card_orderedProfile_mul ξ ha hb ht

theorem sum_weighted_eq_ordered (n : Nat) (f : Config 2 2 → Rat) :
    (∑ ξ ∈ fullyTyped n,
      (Nat.factorial n : Rat) / ((∏ i, ∏ j, Nat.factorial (ξ.c i j) : Nat) : Rat) * f ξ)
      = ∑ a : Fin n → Fin 2, ∑ b : Fin n → Fin 2, f (cSample a b) := by
  classical
  calc
    _ = ∑ ξ ∈ fullyTyped n, ∑ p : (Fin n → Fin 2) × (Fin n → Fin 2)
        with cSample p.1 p.2 = ξ, f ξ := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      rw [← card_orderedProfile_rat hξ]
      simp [orderedProfile, nsmul_eq_mul]
    _ = ∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), f (cSample p.1 p.2) :=
      Finset.sum_fiberwise_of_maps_to' (fun p _ => mem_image.mpr ⟨p, mem_univ _, rfl⟩) f
    _ = _ := Fintype.sum_prod_type _

theorem sum_q_weighted {θA θB ρ : Rat} {πA πB : Fin 2 → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hsA : ∑ i, πA i = 1) (hsB : ∑ j, πB j = 1) (n : Nat) :
    (∑ ξ ∈ fullyTyped n,
      (Nat.factorial n : Rat) / ((∏ i, ∏ j, Nat.factorial (ξ.c i j) : Nat) : Rat) *
        Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ) = 1 := by
  rw [sum_weighted_eq_ordered]
  exact sum_q_ordered hθA hθB hρ hsA hsB n

end Rhone.Computation.CheckerSpec
