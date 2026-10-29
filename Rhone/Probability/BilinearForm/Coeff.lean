/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.BilinearForm.Factor

/-! # The coefficient of the bilinear form is nonzero for `t ≥ 2` -/

@[expose] public section

namespace Rhone.Probability.BilinearForm

open Finset LinearAlgebra.Recursion Config

variable {KA KB : ℕ}

def cf0 (ξ : Config KA KB) : ℤ :=
  (wt0 ξ : ℤ) - (∑ i, (wtA ξ i : ℤ)) - (∑ j, (wtB ξ j : ℤ)) + ∑ i, ∑ j, (wtAB ξ i j : ℤ)

def cfA (ξ : Config KA KB) (i : Fin KA) : ℤ := (wtA ξ i : ℤ) - ∑ j, (wtAB ξ i j : ℤ)

def cfB (ξ : Config KA KB) (j : Fin KB) : ℤ := (wtB ξ j : ℤ) - ∑ i, (wtAB ξ i j : ℤ)

theorem coeff_ne_zero_of_two_le_t (ξ : Config KA KB) (ht : 2 ≤ ξ.t) :
    cf0 ξ ≠ 0 ∨ (∃ i, cfA ξ i ≠ 0) ∨ (∃ j, cfB ξ j ≠ 0) ∨ (∃ i j, wtAB ξ i j ≠ 0) := by
  by_cases h4 : ∃ i j, wtAB ξ i j ≠ 0
  · exact Or.inr (Or.inr (Or.inr h4))
  by_cases h2 : ∃ i, cfA ξ i ≠ 0
  · exact Or.inr (Or.inl h2)
  by_cases h3 : ∃ j, cfB ξ j ≠ 0
  · exact Or.inr (Or.inr (Or.inl h3))
  simp only [not_exists, ne_eq, not_not] at h4 h2 h3
  refine Or.inl ?_
  have hrow : ∀ i : Fin KA, (∑ j, (wtAB ξ i j : ℤ)) = 0 := fun i =>
    Finset.sum_eq_zero fun j _ => by rw [h4 i j]; rfl
  have hcol : ∀ j : Fin KB, (∑ i, (wtAB ξ i j : ℤ)) = 0 := fun j =>
    Finset.sum_eq_zero fun i _ => by rw [h4 i j]; rfl
  have hA : ∀ i : Fin KA, (wtA ξ i : ℤ) = 0 := by
    intro i
    have h := h2 i
    rw [cfA, hrow i, sub_zero] at h
    exact h
  have hB : ∀ j : Fin KB, (wtB ξ j : ℤ) = 0 := by
    intro j
    have h := h3 j
    rw [cfB, hcol j, sub_zero] at h
    exact h
  have e1 : (∑ i, (wtA ξ i : ℤ)) = 0 := Finset.sum_eq_zero fun i _ => hA i
  have e2 : (∑ j, (wtB ξ j : ℤ)) = 0 := Finset.sum_eq_zero fun j _ => hB j
  have e3 : (∑ i, ∑ j, (wtAB ξ i j : ℤ)) = 0 := Finset.sum_eq_zero fun i _ => hrow i
  have hw0 : wt0 ξ ≠ 0 := by
    simp only [wt0]
    intro h
    rcases Nat.mul_eq_zero.mp h with h' | h' <;> omega
  rw [cf0, e1, e2, e3]
  simpa using hw0

theorem two_mul_natCast_sub_two_ne_zero {K : ℕ} (hK : 2 ≤ K) : 2 * (K : ℚ) - 2 ≠ 0 := by
  have h : (2 : ℚ) ≤ (K : ℚ) := by exact_mod_cast hK
  intro hc
  linarith

theorem cf0_cast (ξ : Config KA KB) :
    ((wt0 ξ : ℚ) - (∑ i, (wtA ξ i : ℚ)) - (∑ j, (wtB ξ j : ℚ))
      + ∑ i, ∑ j, (wtAB ξ i j : ℚ)) = ((cf0 ξ : ℤ) : ℚ) := by
  rw [cf0]
  push_cast
  ring

theorem cfA_cast (ξ : Config KA KB) (i : Fin KA) :
    ((wtA ξ i : ℚ) - ∑ j, (wtAB ξ i j : ℚ)) = ((cfA ξ i : ℤ) : ℚ) := by
  rw [cfA]
  push_cast
  ring

theorem cfB_cast (ξ : Config KA KB) (j : Fin KB) :
    ((wtB ξ j : ℚ) - ∑ i, (wtAB ξ i j : ℚ)) = ((cfB ξ j : ℤ) : ℚ) := by
  rw [cfB]
  push_cast
  ring

theorem exists_Pgen_ne_zero (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB) (ht : 2 ≤ ξ.t) :
    ∃ (dA : Fin KA → ℚ) (dB : Fin KB → ℚ),
      LinearAlgebra.BilinearForm.Pgen (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) dA dB ≠ 0 := by
  have hnegA : ((-1 : ℚ)) ^ KA ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnegB : ((-1 : ℚ)) ^ KB ≠ 0 := pow_ne_zero _ (by norm_num)
  rcases coeff_ne_zero_of_two_le_t ξ ht with h | ⟨i₀, h⟩ | ⟨j₀, h⟩ | ⟨i₀, j₀, h⟩
  · refine ⟨LinearAlgebra.BilinearForm.ptNeg KA, LinearAlgebra.BilinearForm.ptNeg KB, ?_⟩
    rw [LinearAlgebra.BilinearForm.Pgen_of_key _ _ _ _
        (fun i => LinearAlgebra.BilinearForm.key_ptNeg i)
        (fun j => LinearAlgebra.BilinearForm.key_ptNeg j),
      LinearAlgebra.BilinearForm.prodAll_ptNeg, LinearAlgebra.BilinearForm.prodAll_ptNeg, cf0_cast]
    exact mul_ne_zero (mul_ne_zero hnegA hnegB) (Int.cast_ne_zero.mpr h)
  · refine ⟨LinearAlgebra.BilinearForm.ptOne i₀, LinearAlgebra.BilinearForm.ptNeg KB, ?_⟩
    rw [LinearAlgebra.BilinearForm.Pgen_of_pt_left _ _ _ _ i₀
        (LinearAlgebra.BilinearForm.prodAll_ptOne i₀)
        (LinearAlgebra.BilinearForm.prodErase_ptOne_self i₀)
        (fun i hi => LinearAlgebra.BilinearForm.prodErase_ptOne_of_ne hi)
            (fun j => LinearAlgebra.BilinearForm.key_ptNeg j),
      LinearAlgebra.BilinearForm.prodAll_ptNeg, LinearAlgebra.BilinearForm.sfac_ptOne, cfA_cast]
    exact neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (two_mul_natCast_sub_two_ne_zero hKA) hnegB)
        (Int.cast_ne_zero.mpr h))
  · refine ⟨LinearAlgebra.BilinearForm.ptNeg KA, LinearAlgebra.BilinearForm.ptOne j₀, ?_⟩
    rw [LinearAlgebra.BilinearForm.Pgen_of_pt_right _ _ _ _ j₀
        (fun i => LinearAlgebra.BilinearForm.key_ptNeg i)
        (LinearAlgebra.BilinearForm.prodAll_ptOne j₀)
        (LinearAlgebra.BilinearForm.prodErase_ptOne_self j₀)
            (fun j hj => LinearAlgebra.BilinearForm.prodErase_ptOne_of_ne hj),
      LinearAlgebra.BilinearForm.prodAll_ptNeg, LinearAlgebra.BilinearForm.sfac_ptOne, cfB_cast]
    exact neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (two_mul_natCast_sub_two_ne_zero hKB) hnegA)
        (Int.cast_ne_zero.mpr h))
  · refine ⟨LinearAlgebra.BilinearForm.ptOne i₀, LinearAlgebra.BilinearForm.ptOne j₀, ?_⟩
    rw [LinearAlgebra.BilinearForm.Pgen_of_pt_both _ _ _ _ i₀ j₀
        (LinearAlgebra.BilinearForm.prodAll_ptOne i₀)
        (LinearAlgebra.BilinearForm.prodErase_ptOne_self i₀)
        (fun i hi => LinearAlgebra.BilinearForm.prodErase_ptOne_of_ne hi)
            (LinearAlgebra.BilinearForm.prodAll_ptOne j₀)
            (LinearAlgebra.BilinearForm.prodErase_ptOne_self j₀)
        (fun j hj => LinearAlgebra.BilinearForm.prodErase_ptOne_of_ne hj),
      LinearAlgebra.BilinearForm.sfac_ptOne, LinearAlgebra.BilinearForm.sfac_ptOne]
    exact mul_ne_zero
      (mul_ne_zero (two_mul_natCast_sub_two_ne_zero hKA) (two_mul_natCast_sub_two_ne_zero hKB))
      (Nat.cast_ne_zero.mpr h)

end Rhone.Probability.BilinearForm
