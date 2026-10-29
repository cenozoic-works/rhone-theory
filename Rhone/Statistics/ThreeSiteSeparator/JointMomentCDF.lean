/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.JointCDFIntegral

/-! # Bivariate moments from joint CDF integrals, without a density assumption -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma unitSquare_power_integrable (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1) (r s : ℕ) :
    Integrable (fun z => z.1^r*z.2^s) ν := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [hν] with z hz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hz.1.1 r),
    abs_of_nonneg (pow_nonneg hz.2.1 s)]
  exact (mul_le_mul (pow_le_one₀ hz.1.1 hz.1.2) (pow_le_one₀ hz.2.1 hz.2.2)
    (pow_nonneg hz.2.1 s) (by norm_num)).trans_eq (one_mul 1)

theorem joint_moment_CDF (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂ν, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1) (r s : ℕ) :
    (∫ z, z.1^(r+1)*z.2^(s+1) ∂ν) =
      (∫ z, z.1^(r+1) ∂ν) + (∫ z, z.2^(s+1) ∂ν) - 1 +
        ((r : ℝ)+1)*((s : ℝ)+1)*weightedJointCDF r s ν := by
  have h1 : Integrable (fun z : ℝ × ℝ => z.1^(r+1)) ν := by
    simpa only [pow_zero, mul_one] using unitSquare_power_integrable ν hν (r+1) 0
  have h2 : Integrable (fun z : ℝ × ℝ => z.2^(s+1)) ν := by
    simpa only [pow_zero, one_mul] using unitSquare_power_integrable ν hν 0 (s+1)
  have h12 := unitSquare_power_integrable ν hν (r+1) (s+1)
  have hA : Integrable (fun z : ℝ × ℝ => 1-z.1^(r+1)) ν := (integrable_const 1).sub h1
  have hB : Integrable (fun z : ℝ × ℝ => 1-z.1^(r+1)-z.2^(s+1)) ν := hA.sub h2
  have hd : (r : ℝ)+1 ≠ 0 := by positivity
  have he : (s : ℝ)+1 ≠ 0 := by positivity
  have hp (z : ℝ × ℝ) :
      (((r : ℝ)+1)*((s : ℝ)+1))*
        (((1-z.1^(r+1))/((r : ℝ)+1))*((1-z.2^(s+1))/((s : ℝ)+1))) =
      1-z.1^(r+1)-z.2^(s+1)+z.1^(r+1)*z.2^(s+1) := by
    field_simp
    ring
  have ht : ((r : ℝ)+1)*((s : ℝ)+1)*weightedJointCDF r s ν =
      1-(∫ z, z.1^(r+1) ∂ν)-(∫ z, z.2^(s+1) ∂ν)+
        (∫ z, z.1^(r+1)*z.2^(s+1) ∂ν) := by
    rw [weightedJointCDF_eq_tail_product ν hν, ← integral_const_mul]
    simp_rw [hp]
    rw [integral_add hB h12, integral_sub hA h2, integral_sub (integrable_const 1) h1]
    simp
  linarith

end Rhone.Statistics.ThreeSiteSeparator
