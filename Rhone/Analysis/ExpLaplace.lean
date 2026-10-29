/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Probability.Distributions.Exponential

/-! # The Laplace transform of the standard exponential law -/

@[expose] public section

namespace Rhone.Analysis.ExpLaplace

open MeasureTheory ProbabilityTheory

theorem lintegral_exp_neg_expMeasure_one {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (-max 0 (a * t))) ∂expMeasure 1 =
      ENNReal.ofReal (1 + a)⁻¹ := by
  have h1a : (0 : ℝ) < 1 + a := by linarith
  have hpt : ∀ t : ℝ, gammaPDF 1 1 t * ENNReal.ofReal (Real.exp (-max 0 (a * t))) =
      ENNReal.ofReal (1 + a)⁻¹ * gammaPDF 1 (1 + a) t := by
    intro t
    by_cases ht : 0 ≤ t
    · simp only [gammaPDF_of_nonneg ht, Real.Gamma_one, sub_self, Real.rpow_zero,
        Real.rpow_one, div_one, mul_one, one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        max_eq_right (mul_nonneg ha ht), ← Real.exp_add, ← mul_assoc,
        inv_mul_cancel₀ h1a.ne', one_mul]
      congr 2
      ring
    · rw [gammaPDF_of_neg (not_le.1 ht), gammaPDF_of_neg (not_le.1 ht), zero_mul, mul_zero]
  have hm : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hf : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-max 0 (a * t))) := by
    fun_prop
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hm hf]
  simp only [Pi.mul_apply, hpt]
  have hg : Measurable (gammaPDF 1 (1 + a)) := (measurable_gammaPDFReal 1 (1 + a)).ennreal_ofReal
  rw [lintegral_const_mul _ hg, lintegral_gammaPDF_eq_one one_pos h1a, mul_one]

end Rhone.Analysis.ExpLaplace
