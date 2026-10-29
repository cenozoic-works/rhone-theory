/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.Closure.Orthant
public import Rhone.Probability.BilinearForm.Converse
public import Rhone.Coalescent.Rational.Expansion

/-! # Real admissible parameter points for the two-locus closed form, per configuration -/

@[expose] public section

namespace Rhone.Coalescent.Closure

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config LinearAlgebra.BilinearForm
    Probability.BilinearForm

variable {KA KB : ℕ}

noncomputable def thAOf (x : Fin KA ⊕ Fin KB → ℝ) : ℝ := ∑ i : Fin KA, x (Sum.inl i)

noncomputable def thBOf (x : Fin KA ⊕ Fin KB → ℝ) : ℝ := ∑ j : Fin KB, x (Sum.inr j)

noncomputable def piAOf (x : Fin KA ⊕ Fin KB → ℝ) (i : Fin KA) : ℝ := x (Sum.inl i) / thAOf x

noncomputable def piBOf (x : Fin KA ⊕ Fin KB → ℝ) (j : Fin KB) : ℝ := x (Sum.inr j) / thBOf x

variable {x : Fin KA ⊕ Fin KB → ℝ}

theorem thAOf_pos (hKA : 0 < KA) (hx : ∀ s, 0 < x s) : 0 < thAOf (KB := KB) x :=
  Finset.sum_pos (fun _ _ => hx _) ⟨⟨0, hKA⟩, Finset.mem_univ _⟩

theorem thBOf_pos (hKB : 0 < KB) (hx : ∀ s, 0 < x s) : 0 < thBOf (KA := KA) x :=
  Finset.sum_pos (fun _ _ => hx _) ⟨⟨0, hKB⟩, Finset.mem_univ _⟩

theorem piAOf_pos (hKA : 0 < KA) (hx : ∀ s, 0 < x s) (i : Fin KA) :
    0 < piAOf (KB := KB) x i :=
  div_pos (hx _) (thAOf_pos hKA hx)

theorem piBOf_pos (hKB : 0 < KB) (hx : ∀ s, 0 < x s) (j : Fin KB) :
    0 < piBOf (KA := KA) x j :=
  div_pos (hx _) (thBOf_pos hKB hx)

theorem sum_piAOf (hKA : 0 < KA) (hx : ∀ s, 0 < x s) :
    (∑ i : Fin KA, piAOf (KB := KB) x i) = 1 := by
  simp only [piAOf]
  rw [← Finset.sum_div]
  exact div_self (thAOf_pos hKA hx).ne'

theorem sum_piBOf (hKB : 0 < KB) (hx : ∀ s, 0 < x s) :
    (∑ j : Fin KB, piBOf (KA := KA) x j) = 1 := by
  simp only [piBOf]
  rw [← Finset.sum_div]
  exact div_self (thBOf_pos hKB hx).ne'

theorem thAOf_mul_piAOf (hKA : 0 < KA) (hx : ∀ s, 0 < x s) (i : Fin KA) :
    thAOf (KB := KB) x * piAOf x i = x (Sum.inl i) := by
  rw [piAOf, mul_div_cancel₀ _ (thAOf_pos hKA hx).ne']

theorem thBOf_mul_piBOf (hKB : 0 < KB) (hx : ∀ s, 0 < x s) (j : Fin KB) :
    thBOf (KA := KA) x * piBOf x j = x (Sum.inr j) := by
  rw [piBOf, mul_div_cancel₀ _ (thBOf_pos hKB hx).ne']

theorem qOne_ne_zero_of_pos {K : ℕ} {θ : ℝ} {π : Fin K → ℝ} (hθ : 0 < θ)
    (hπ : ∀ i, 0 < π i) (m : Fin K → ℕ) : qOne θ π m ≠ 0 := by
  rw [qOne]
  exact div_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => (rising_pos (mul_pos hθ (hπ i)) _).ne')
    (rising_ne_zero hθ _)

theorem eval₂_dpolyA (ξ : Config KA KB) (i : Fin KA) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (dpolyA ξ i)
      = x (Sum.inl i) + ((ξ.mA i : ℕ) : ℝ) - 1 := by
  rw [dpolyA, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, eq_ratCast]
  push_cast
  ring

theorem eval₂_dpolyB (ξ : Config KA KB) (j : Fin KB) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (dpolyB ξ j)
      = x (Sum.inr j) + ((ξ.mB j : ℕ) : ℝ) - 1 := by
  rw [dpolyB, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, eq_ratCast]
  push_cast
  ring

theorem dvalA_eq_eval₂ (hKA : 0 < KA) (hx : ∀ s, 0 < x s) (ξ : Config KA KB) (i : Fin KA) :
    dvalA (thAOf x) (piAOf x) ξ i
      = MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (dpolyA ξ i) := by
  rw [eval₂_dpolyA, dvalA, thAOf_mul_piAOf hKA hx]

theorem dvalB_eq_eval₂ (hKB : 0 < KB) (hx : ∀ s, 0 < x s) (ξ : Config KA KB) (j : Fin KB) :
    dvalB (thBOf x) (piBOf x) ξ j
      = MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (dpolyB ξ j) := by
  rw [eval₂_dpolyB, dvalB, thBOf_mul_piBOf hKB hx]

theorem twoQ1_ne_zero_of_eval_ne_zero (hKA : 0 < KA) (hKB : 0 < KB) (hx : ∀ s, 0 < x s)
    (ξ : Config KA KB)
    (hne : MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
        (Pgen (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) (dpolyA ξ) (dpolyB ξ)) ≠ 0) :
    Rhone.Probability.RecombinationExpansion.twoQ1 (thAOf x) (thBOf x) (piAOf x) (piBOf x) ξ ≠ 0 :=
        by
  have hθA := thAOf_pos (KB := KB) hKA hx
  have hθB := thBOf_pos (KA := KA) hKB hx
  have hkey := twoQ1_mul_prodAll (θA := thAOf x) (θB := thBOf x) (πA := piAOf x)
    (πB := piBOf x) (sum_piAOf hKA hx) (sum_piBOf hKB hx) ξ
    (rising_ne_zero hθA _) (rising_ne_zero hθB _)
  have hPg : Pgen (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) (dvalA (thAOf x) (piAOf x) ξ)
      (dvalB (thBOf x) (piBOf x) ξ) ≠ 0 := by
    have hmap := map_Pgen (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x)
      (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) (dpolyA ξ) (dpolyB ξ)
    simp only [MvPolynomial.coe_eval₂Hom] at hmap
    rw [← funext (dvalA_eq_eval₂ hKA hx ξ), ← funext (dvalB_eq_eval₂ hKB hx ξ)] at hmap
    rw [← hmap]
    exact hne
  intro hzero
  rw [hzero, zero_mul] at hkey
  exact mul_ne_zero (mul_ne_zero (qOne_ne_zero_of_pos hθA (piAOf_pos hKA hx) _)
    (qOne_ne_zero_of_pos hθB (piBOf_pos hKB hx) _)) hPg hkey.symm

theorem exists_poly_ne_zero_forcing (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB)
    (ht : 2 ≤ ξ.t) :
    ∃ P : MvPolynomial (Fin KA ⊕ Fin KB) ℝ, P ≠ 0 ∧
      ∀ y : Fin KA ⊕ Fin KB → ℝ, (∀ s, 0 < y s) → MvPolynomial.eval y P ≠ 0 →
        Rhone.Probability.RecombinationExpansion.twoQ1 (thAOf y) (thBOf y) (piAOf y) (piBOf y) ξ ≠
            0 := by
  refine ⟨MvPolynomial.map (algebraMap ℚ ℝ)
    (Pgen (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) (dpolyA ξ) (dpolyB ξ)), ?_, ?_⟩
  · intro h
    exact Pgen_dpoly_ne_zero hKA hKB ξ ht
      (MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
        (by rw [h, map_zero]))
  · intro y hy hev
    refine twoQ1_ne_zero_of_eval_ne_zero (by omega) (by omega) hy ξ ?_
    rwa [MvPolynomial.eval_map] at hev

theorem exists_admissible_twoQ1_ne_zero (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB)
    (ht : 2 ≤ ξ.t) :
    ∃ (θA θB : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ), 0 < θA ∧ 0 < θB ∧
      (∀ i, 0 < πA i) ∧ (∑ i, πA i = 1) ∧ (∀ j, 0 < πB j) ∧ (∑ j, πB j = 1) ∧
      Rhone.Probability.RecombinationExpansion.twoQ1 θA θB πA πB ξ ≠ 0 := by
  obtain ⟨P, hP, hforce⟩ := exists_poly_ne_zero_forcing hKA hKB ξ ht
  obtain ⟨y, hy, hev⟩ := Analysis.Closure.exists_pos_eval_ne_zero hP
  exact ⟨thAOf y, thBOf y, piAOf y, piBOf y, thAOf_pos (by omega) hy,
    thBOf_pos (by omega) hy, piAOf_pos (by omega) hy, sum_piAOf (by omega) hy,
    piBOf_pos (by omega) hy, sum_piBOf (by omega) hy, hforce y hy hev⟩

end Rhone.Coalescent.Closure
