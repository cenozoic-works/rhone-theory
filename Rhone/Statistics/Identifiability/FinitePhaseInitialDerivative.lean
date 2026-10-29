/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseSurvivalProfile

/-! # Initial derivative of the finite-phase density factor in terms of exit rates -/

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix BigOperators
namespace Rhone.Statistics.Identifiability.FinitePhase.Model
variable {n m : ℕ}

lemma initial_derivative_eq (M : Model n m) :
    M.d 0 = -(dotProduct M.α (exitRate M.A)) / 3 := by
  have hrow (i : Fin n) : (M.N *ᵥ M.h) (Fin.castAdd m i) = -(exitRate M.A i) / 3 := by
    have hf := congrFun M.flux i
    simp only [Matrix.mulVec, dotProduct, mul_one] at hf
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, h,
      Fin.addCases_left, Fin.addCases_right, M.pre_pre, M.pre_post, mul_one]
    rw [← Finset.sum_mul, hf]
    simp only [exitRate, Matrix.mulVec, dotProduct, mul_one, Pi.neg_apply]
    ring
  simp only [d, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, γ, initial,
    dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    zero_mul, Finset.sum_const_zero, add_zero, hrow]
  calc
    _ = ∑ i, -(M.α i * exitRate M.A i) / 3 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib]

lemma initial_derivative_zero_of_exit (M : Model n m)
    (hzero : dotProduct M.α (exitRate M.A) = 0) : M.d 0 = 0 := by
  rw [M.initial_derivative_eq, hzero]
  norm_num

end Rhone.Statistics.Identifiability.FinitePhase.Model
