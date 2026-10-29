/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.OrderedSampleCount

/-! # The `|Aut(c)|` half: orbit and stabilizer of the allele-relabelling action -/

@[expose] public section

namespace Rhone.Probability.OrbitCounts

open Finset LinearAlgebra.Recursion InfiniteAlleles

variable {KA KB : ℕ}

local instance instDecidableEqConfig : DecidableEq (Config KA KB) := fun ξ η =>
  decidable_of_iff (ξ.a = η.a ∧ ξ.b = η.b ∧ ξ.c = η.c)
    ⟨fun h => Config.ext h.1 h.2.1 h.2.2, fun h => by subst h; exact ⟨rfl, rfl, rfl⟩⟩

theorem relabel_one (ξ : Config KA KB) :
    relabel (1 : Equiv.Perm (Fin KA)) (1 : Equiv.Perm (Fin KB)) ξ = ξ := rfl

theorem relabel_relabel (σ σ' : Equiv.Perm (Fin KA)) (τ τ' : Equiv.Perm (Fin KB))
    (ξ : Config KA KB) :
    relabel σ' τ' (relabel σ τ ξ) = relabel (σ * σ') (τ * τ') ξ := rfl

def relabelOrbit (ξ : Config KA KB) : Finset (Config KA KB) :=
  Finset.univ.image fun p : Equiv.Perm (Fin KA) × Equiv.Perm (Fin KB) => relabel p.1 p.2 ξ

def aut (ξ : Config KA KB) : Finset (Equiv.Perm (Fin KA) × Equiv.Perm (Fin KB)) :=
  Finset.univ.filter fun p => relabel p.1 p.2 ξ = ξ

theorem mem_relabelOrbit {ξ η : Config KA KB} :
    η ∈ relabelOrbit ξ ↔ ∃ σ τ, relabel σ τ ξ = η := by
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
    exact ⟨p.1, p.2, hp⟩
  · rintro ⟨σ, τ, rfl⟩
    exact Finset.mem_image.mpr ⟨(σ, τ), Finset.mem_univ _, rfl⟩

theorem mem_aut {ξ : Config KA KB} {p : Equiv.Perm (Fin KA) × Equiv.Perm (Fin KB)} :
    p ∈ aut ξ ↔ relabel p.1 p.2 ξ = ξ := by
  rw [aut, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem self_mem_relabelOrbit (ξ : Config KA KB) : ξ ∈ relabelOrbit ξ :=
  mem_relabelOrbit.mpr ⟨1, 1, relabel_one ξ⟩

theorem one_mem_aut (ξ : Config KA KB) : (1, 1) ∈ aut ξ := mem_aut.mpr (relabel_one ξ)

theorem card_aut_pos (ξ : Config KA KB) : 0 < (aut ξ).card :=
  Finset.card_pos.mpr ⟨(1, 1), one_mem_aut ξ⟩

theorem card_relabelOrbit_mul_card_aut (ξ : Config KA KB) :
    (relabelOrbit ξ).card * (aut ξ).card = Nat.factorial KA * Nat.factorial KB := by
  classical
  have hmaps : ∀ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin KA) × Equiv.Perm (Fin KB))),
      relabel p.1 p.2 ξ ∈ relabelOrbit ξ := fun p _ => mem_relabelOrbit.mpr ⟨p.1, p.2, rfl⟩
  have hfib : ∀ η ∈ relabelOrbit ξ,
      (Finset.univ.filter fun p : Equiv.Perm (Fin KA) × Equiv.Perm (Fin KB) =>
        relabel p.1 p.2 ξ = η).card = (aut ξ).card := by
    intro η hη
    obtain ⟨σ₀, τ₀, hστ⟩ := mem_relabelOrbit.mp hη
    refine (Finset.card_bij (fun q _ => (q.1 * σ₀, q.2 * τ₀)) ?_ ?_ ?_).symm
    · intro q hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← relabel_relabel q.1 σ₀ q.2 τ₀ ξ, mem_aut.mp hq, hστ]
    · intro q _ q' _ heq
      have h1 : q.1 * σ₀ = q'.1 * σ₀ := congrArg Prod.fst heq
      have h2 : q.2 * τ₀ = q'.2 * τ₀ := congrArg Prod.snd heq
      exact Prod.ext (mul_right_cancel h1) (mul_right_cancel h2)
    · intro p hp
      have hpη : relabel p.1 p.2 ξ = η := (Finset.mem_filter.mp hp).2
      refine ⟨(p.1 * σ₀⁻¹, p.2 * τ₀⁻¹), mem_aut.mpr ?_, ?_⟩
      · rw [← relabel_relabel p.1 σ₀⁻¹ p.2 τ₀⁻¹ ξ, hpη, ← hστ,
          relabel_relabel σ₀ σ₀⁻¹ τ₀ τ₀⁻¹ ξ, mul_inv_cancel, mul_inv_cancel, relabel_one]
      · exact Prod.ext (inv_mul_cancel_right _ _) (inv_mul_cancel_right _ _)
  have hcount : (Finset.univ : Finset (Equiv.Perm (Fin KA) × Equiv.Perm (Fin KB))).card
      = Nat.factorial KA * Nat.factorial KB := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
      Fintype.card_fin, Fintype.card_fin]
  have key : (Finset.univ : Finset (Equiv.Perm (Fin KA) × Equiv.Perm (Fin KB))).card
      = (relabelOrbit ξ).card * (aut ξ).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hfib, Finset.sum_const,
      smul_eq_mul]
  rw [← key, hcount]

theorem card_relabelOrbit_eq_div (ξ : Config KA KB) :
    ((relabelOrbit ξ).card : ℚ)
      = (Nat.factorial KA * Nat.factorial KB : ℕ) / ((aut ξ).card : ℚ) := by
  have hne : ((aut ξ).card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (card_aut_pos ξ).ne'
  rw [eq_div_iff hne]
  exact_mod_cast card_relabelOrbit_mul_card_aut ξ

section Prob

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

theorem aut_card_mul_sum_PIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ξ : Config KA KB) :
    ((aut ξ).card : F) * ∑ η ∈ relabelOrbit ξ, PIA hθA hθB hρ η
      = (Nat.factorial KA * Nat.factorial KB : ℕ) * PIA hθA hθB hρ ξ := by
  have h1 : ∑ η ∈ relabelOrbit ξ, PIA hθA hθB hρ η
      = ((relabelOrbit ξ).card : F) * PIA hθA hθB hρ ξ :=
    Rhone.Probability.InfiniteAlleles.sum_PIA_of_relabelClass hθA hθB hρ ξ (relabelOrbit ξ) fun η hη
        => by
      obtain ⟨σ, τ, hστ⟩ := mem_relabelOrbit.mp hη
      exact ⟨σ, τ, hστ.symm⟩
  have h2 : ((aut ξ).card : F) * ((relabelOrbit ξ).card : F)
      = ((Nat.factorial KA * Nat.factorial KB : ℕ) : F) := by
    rw [← Nat.cast_mul, mul_comm ((aut ξ).card) ((relabelOrbit ξ).card),
      card_relabelOrbit_mul_card_aut]
  rw [h1, ← mul_assoc, h2]

end Prob

end Rhone.Probability.OrbitCounts
