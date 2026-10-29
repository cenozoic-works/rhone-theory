/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TwoParameterMarkovFlow
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-! # Time-ordered Duhamel formula for continuous finite matrix generators -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators Topology Matrix.Norms.Operator

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inhomogeneousTransition_interpolation_hasDerivAt
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, Continuous (fun t => A t i j))
    (hB : ∀ i j, Continuous (fun t => B t i j)) (s t u : ℝ) :
    HasDerivAt (fun v => inhomogeneousTransition A s v * inhomogeneousTransition B v t)
      (inhomogeneousTransition A s u * (A u - B u) * inhomogeneousTransition B u t) u := by
  apply hasDerivAt_pi.mpr; intro i
  apply hasDerivAt_pi.mpr; intro j
  have h := finiteMatrixProduct_hasDerivAt
    (inhomogeneousTransition A s) (fun v => inhomogeneousTransition B v t)
    (fun v => inhomogeneousTransition A s v * A v)
    (fun v => -(B v * inhomogeneousTransition B v t))
    (fun v => inhomogeneousTransition_hasDerivAt_right A hA s v)
    (fun v => inhomogeneousTransition_hasDerivAt_left B hB v t) u i j
  simpa only [Matrix.mul_neg, ← Matrix.mul_assoc, ← sub_eq_add_neg,
    ← Matrix.sub_mul, ← Matrix.mul_sub] using h

theorem inhomogeneousTransition_sub_eq_integral
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, Continuous (fun t => A t i j))
    (hB : ∀ i j, Continuous (fun t => B t i j)) (s t : ℝ) :
    inhomogeneousTransition A s t - inhomogeneousTransition B s t =
      ∫ u in s..t, inhomogeneousTransition A s u * (A u - B u) *
        inhomogeneousTransition B u t := by
  have hAc : Continuous A := continuous_pi fun i => continuous_pi (hA i)
  have hBc : Continuous B := continuous_pi fun i => continuous_pi (hB i)
  have hc : Continuous (fun u => inhomogeneousTransition A s u * (A u - B u) *
      inhomogeneousTransition B u t) := by
    exact (((inhomogeneousTransition_continuous A hA).comp
      (continuous_const.prodMk continuous_id)).mul (hAc.sub hBc)).mul
      ((inhomogeneousTransition_continuous B hB).comp (continuous_id.prodMk continuous_const))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => inhomogeneousTransition_interpolation_hasDerivAt A B hA hB s t u)
    (hc.intervalIntegrable s t)
  simpa only [inhomogeneousTransition_self A hA, inhomogeneousTransition_self B hB,
    Matrix.mul_one, Matrix.one_mul] using h.symm

theorem finiteMatrix_norm_le_one_of_substochastic (P : Matrix ι ι ℝ)
    (hn : ∀ i j, 0 ≤ P i j) (hr : ∀ i, ∑ j, P i j ≤ 1) : ‖P‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  suffices h : (Finset.univ.sup fun i : ι => ∑ j : ι, ‖P i j‖₊) ≤ 1 by
    exact_mod_cast h
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (hn i _)] using hr i

theorem inhomogeneousTransition_norm_sub_le_integral
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, Continuous (fun t => A t i j))
    (hB : ∀ i j, Continuous (fun t => B t i j)) {s t : ℝ} (hst : s ≤ t)
    (hAc : ∀ u ∈ Icc s t, ‖inhomogeneousTransition A s u‖ ≤ 1)
    (hBc : ∀ u ∈ Icc s t, ‖inhomogeneousTransition B u t‖ ≤ 1) :
    ‖inhomogeneousTransition A s t - inhomogeneousTransition B s t‖ ≤
      ∫ u in s..t, ‖A u - B u‖ := by
  rw [inhomogeneousTransition_sub_eq_integral A B hA hB]
  apply intervalIntegral.norm_integral_le_of_norm_le hst
  · apply Filter.Eventually.of_forall
    intro u hu
    have hu' : u ∈ Icc s t := ⟨hu.1.le, hu.2⟩
    calc
      ‖inhomogeneousTransition A s u * (A u - B u) * inhomogeneousTransition B u t‖
          ≤ ‖inhomogeneousTransition A s u‖ * ‖A u - B u‖ *
              ‖inhomogeneousTransition B u t‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖A u - B u‖ * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hAc u hu') (norm_nonneg _))
          (hBc u hu') (norm_nonneg _) (by positivity)
      _ = ‖A u - B u‖ := by ring
  · have hAc' : Continuous A := continuous_pi fun i => continuous_pi (hA i)
    have hBc' : Continuous B := continuous_pi fun i => continuous_pi (hB i)
    exact (hAc'.sub hBc').norm.intervalIntegrable s t

theorem inhomogeneousTransition_norm_sub_le_integral_of_substochastic
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, Continuous (fun t => A t i j))
    (hB : ∀ i j, Continuous (fun t => B t i j)) {s t : ℝ} (hst : s ≤ t)
    (hAn : ∀ u ∈ Icc s t, ∀ i j, 0 ≤ inhomogeneousTransition A s u i j)
    (hAr : ∀ u ∈ Icc s t, ∀ i, ∑ j, inhomogeneousTransition A s u i j ≤ 1)
    (hBn : ∀ u ∈ Icc s t, ∀ i j, 0 ≤ inhomogeneousTransition B u t i j)
    (hBr : ∀ u ∈ Icc s t, ∀ i, ∑ j, inhomogeneousTransition B u t i j ≤ 1) :
    ‖inhomogeneousTransition A s t - inhomogeneousTransition B s t‖ ≤
      ∫ u in s..t, ‖A u - B u‖ := by
  exact inhomogeneousTransition_norm_sub_le_integral A B hA hB hst
    (fun u hu => finiteMatrix_norm_le_one_of_substochastic _ (hAn u hu) (hAr u hu))
    (fun u hu => finiteMatrix_norm_le_one_of_substochastic _ (hBn u hu) (hBr u hu))

theorem inhomogeneousTransition_norm_sub_le_integral_of_subgenerator
    (A B : ℝ → Matrix ι ι ℝ)
    (hA : ∀ i j, Continuous (fun t => A t i j))
    (hB : ∀ i j, Continuous (fun t => B t i j))
    (hAn : ∀ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ A u i j)
    (hAr : ∀ u, 0 ≤ u → ∀ i, ∑ j, A u i j ≤ 0)
    (hBn : ∀ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ B u i j)
    (hBr : ∀ u, 0 ≤ u → ∀ i, ∑ j, B u i j ≤ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖inhomogeneousTransition A s t - inhomogeneousTransition B s t‖ ≤
      ∫ u in s..t, ‖A u - B u‖ := by
  apply inhomogeneousTransition_norm_sub_le_integral_of_substochastic A B hA hB hst
  · exact fun u hu => inhomogeneousTransition_nonneg A hA hAn hs hu.1
  · exact fun u hu => inhomogeneousTransition_row_sum_le_one A hA hAn hAr hs hu.1
  · exact fun u hu => inhomogeneousTransition_nonneg B hB hBn (hs.trans hu.1) hu.2
  · exact fun u hu => inhomogeneousTransition_row_sum_le_one B hB hBn hBr
      (hs.trans hu.1) hu.2

end Rhone.Statistics.Identifiability
