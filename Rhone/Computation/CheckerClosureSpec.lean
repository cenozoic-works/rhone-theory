/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.LinearAlgebra.Recursion.Exist

/-! # Uniqueness on a finite marginal closure -/

@[expose] public section
namespace Rhone.Computation.CheckerSpec

open Rhone.LinearAlgebra LinearAlgebra.Recursion Finset

variable {KA KB : Nat} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

def InClosure (N : Nat) (ξ : Rhone.LinearAlgebra.Recursion.Config KA KB) : Prop :=
  ξ.nA ≤ N ∧ ξ.nB ≤ N

theorem closure_unique {N : Nat} {f g : Rhone.LinearAlgebra.Recursion.Config KA KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hbd : ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ → ξ.n ≤ 1 → f ξ = g ξ)
    (hf : ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ → 2 ≤ ξ.n →
      diag θA θB ρ ξ * f ξ = rhs θA θB ρ πA πB f ξ)
    (hg : ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ → 2 ≤ ξ.n →
      diag θA θB ρ ξ * g ξ = rhs θA θB ρ πA πB g ξ) :
    ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ → f ξ = g ξ := by
  classical
  let h : Rhone.LinearAlgebra.Recursion.Config KA KB → F :=
    fun ξ => if InClosure N ξ then f ξ - g ξ else 0
  have hboundary : ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB,
      ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ 2 * N → h ξ = 0 := by
    intro ξ hn _
    by_cases hc : InClosure N ξ
    · simp only [h, ite_eq_left hc, hbd ξ hc hn, sub_self]
    · simp only [h, ite_eq_right hc]
  have hequations : ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ 2 *
      N →
      (∀ η : Rhone.LinearAlgebra.Recursion.Config KA KB, η.nA + η.nB < ξ.nA + ξ.nB → h η = 0) →
      diag θA θB ρ ξ * h ξ =
        (∑ i, ∑ j, ((ξ.coalAB i j : Nat) : F) * h (ξ.mergeAB i j))
          + ρ * ∑ i, ∑ j, ((ξ.c i j : Nat) : F) * h (ξ.split i j) := by
    intro ξ hn _ hbelow
    by_cases hc : InClosure N ξ
    · have hcongr : rhs θA θB ρ πA πB h ξ =
          rhs θA θB ρ πA πB (fun η => f η - g η) ξ := by
        apply rhs_congr
        intro η ha hb
        have hη : InClosure N η := ⟨ha.trans hc.1, hb.trans hc.2⟩
        simp only [h, ite_eq_left hη]
      have hrec : diag θA θB ρ ξ * h ξ = rhs θA θB ρ πA πB h ξ := by
        rw [hcongr, rhs_sub]
        simp only [h, ite_eq_left hc, mul_sub, hf ξ hc hn, hg ξ hc hn]
      rw [hrec]
      exact rhs_of_vanishing_below θA θB ρ πA πB ξ
        (fun η ha hb hstrict => hbelow η (by omega))
    · have hmerge : (∑ i, ∑ j, ((ξ.coalAB i j : Nat) : F) * h (ξ.mergeAB i j)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        by_cases ha : ξ.a i = 0
        · rw [ξ.coalAB_eq_zero_left j ha]; simp
        by_cases hb : ξ.b j = 0
        · rw [ξ.coalAB_eq_zero_right i hb]; simp
        obtain ⟨ea, eb⟩ := ξ.mergeAB_same ha hb
        have hnot : ¬ InClosure N (ξ.mergeAB i j) := by
          intro hm
          apply hc
          exact ⟨ea ▸ hm.1, eb ▸ hm.2⟩
        simp only [h, ite_eq_right hnot, mul_zero]
      have hsplit : (∑ i, ∑ j, ((ξ.c i j : Nat) : F) * h (ξ.split i j)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        by_cases hz : ξ.c i j = 0
        · rw [hz]; simp
        obtain ⟨ea, eb⟩ := ξ.split_same hz
        have hnot : ¬ InClosure N (ξ.split i j) := by
          intro hm
          apply hc
          exact ⟨ea ▸ hm.1, eb ▸ hm.2⟩
        simp only [h, ite_eq_right hnot, mul_zero]
      simp only [h, ite_eq_right hc, hmerge, hsplit, mul_zero, zero_add]
  have hzero := within_block_eq_zero hθA hθB hρ
    (fun _ => le_rfl) hboundary hequations
  intro ξ hc
  have hz := hzero ξ (by have ha := hc.1; have hb := hc.2; omega)
  simpa only [h, ite_eq_left hc, sub_eq_zero] using hz

theorem closure_eq_q {N : Nat} {f : Rhone.LinearAlgebra.Recursion.Config KA KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hbd : ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ → ξ.n ≤ 1 →
      f ξ = q (πA := πA) (πB := πB) hθA hθB hρ ξ)
    (hf : ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ → 2 ≤ ξ.n →
      diag θA θB ρ ξ * f ξ = rhs θA θB ρ πA πB f ξ) :
    ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ →
      f ξ = q (πA := πA) (πB := πB) hθA hθB hρ ξ := by
  apply closure_unique hθA hθB hρ hbd hf
  intro ξ _ hn
  exact (q_isSolution (πA := πA) (πB := πB) hθA hθB hρ).recursion ξ hn

end Rhone.Computation.CheckerSpec
