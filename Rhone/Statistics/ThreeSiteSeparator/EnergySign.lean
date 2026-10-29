/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.EnergyIdentity
public import Rhone.Statistics.ThreeSiteSeparator.CDFKernel

/-! # Nonpositive energy for continuous distribution functions on the positive half-line -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma weight_eq_cdfKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    {F : ℝ → ℝ} (hF : Continuous F) (he : ∀ x, F x = μ.real (Iic x))
    {x : ℝ} (hx : 0 ≤ x) : weight F x = cdfKernel μ x := by
  have h1 : IntervalIntegrable (fun y : ℝ => 373275*x^4*(y*F y)) volume 0 x :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun y : ℝ => 926100*x^2*(y^3*F y)) volume 0 x :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  have h5 : IntervalIntegrable (fun y : ℝ => 216405*(y^5*F y)) volume 0 x :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  have h13 : IntervalIntegrable
      (fun y : ℝ => 373275*x^4*(y*F y) - 926100*x^2*(y^3*F y)) volume 0 x :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  unfold cdfKernel
  simp_rw [← he]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  have hp : (fun y => F y * kernel x y) =
      (fun y => 373275*x^4*(y*F y) - 926100*x^2*(y^3*F y) + 216405*(y^5*F y)) := by
    funext y
    unfold kernel
    ring
  rw [hp, intervalIntegral.integral_add h13 h5, intervalIntegral.integral_sub h1 h3]
  simp only [intervalIntegral.integral_const_mul, weight, weightedPrimitive, pow_one]

lemma weight_nonpos_of_cdf (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, 0 ≤ z) {F : ℝ → ℝ} (hF : Continuous F)
    (he : ∀ x, F x = μ.real (Iic x)) {x : ℝ} (hx : 0 ≤ x) : weight F x ≤ 0 := by
  rw [weight_eq_cdfKernel μ hF he hx]
  exact cdfKernel_nonpos μ hμ x

theorem cdf_functional_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, 0 ≤ z) {F : ℝ → ℝ} (hF : Continuous F)
    (he : ∀ x, F x = μ.real (Iic x)) :
    cdfFunctional F + 384 ≤
      boundary (weightedPrimitive 1 (fun t => F t - t) 1)
        (weightedPrimitive 3 (fun t => F t - t) 1)
        (weightedPrimitive 5 (fun t => F t - t) 1) := by
  have hneg : (∫ x in (0 : ℝ)..1, (F x - x)^2*weight F x) ≤ 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (weight_nonpos_of_cdf μ hμ hF he hx.1.le)
  have hpos : 0 ≤ ∫ x in (0 : ℝ)..1,
      x^3*(weightedPrimitive 1 (fun t => F t - t) x)^2 := by
    apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    intro x hx
    exact mul_nonneg (pow_nonneg hx.1 3) (sq_nonneg _)
  have hi := cdf_energy_identity hF
  linarith

end Rhone.Statistics.ThreeSiteSeparator
