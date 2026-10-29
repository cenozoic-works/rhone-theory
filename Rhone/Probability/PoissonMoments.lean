/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Measurability and moments of Poisson mutation counts -/

@[expose] public section
namespace Rhone.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem measurable_poissonMeasure :
    Measurable (poissonMeasure : ℝ≥0 → Measure ℕ) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [poissonMeasure, Measure.sum_apply _ hs, Measure.smul_apply]
  apply Measurable.tsum
  intro k
  apply Measurable.mul_const
  fun_prop

theorem poisson_hasSum_count (r : ℝ≥0) :
    HasSum (fun k : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ k /
    (k.factorial : ℝ) * (k : ℝ)) (r : ℝ) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, sub_zero]
  convert (hasSum_one_poissonMeasure r).mul_left (r : ℝ) using 1
  · funext k
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    field_simp
  · simp

theorem poisson_integral_count (r : ℝ≥0) :
    ∫ k : ℕ, (k : ℝ) ∂poissonMeasure r = r := by
  have hs := poisson_hasSum_count r
  have hint : Integrable (fun k : ℕ => (k : ℝ)) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hs.summable
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using hs.tsum_eq

theorem poisson_hasSum_count_factorial_two (r : ℝ≥0) :
    HasSum (fun k : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ k /
      (k.factorial : ℝ) * ((k : ℝ) * ((k : ℝ) - 1))) ((r : ℝ) ^ 2) := by
  apply (hasSum_nat_add_iff' 2).mp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, sub_self, sub_zero]
  convert (hasSum_one_poissonMeasure r).mul_left ((r : ℝ) ^ 2) using 1
  · funext k
    rw [pow_succ, pow_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · simp

theorem poisson_integral_count_sq (r : ℝ≥0) :
    ∫ k : ℕ, (k : ℝ) ^ 2 ∂poissonMeasure r = (r : ℝ) ^ 2 + r := by
  have hs := (poisson_hasSum_count_factorial_two r).add (poisson_hasSum_count r)
  have he (k : ℕ) :
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ) *
        ((k : ℝ) * ((k : ℝ) - 1)) +
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ) * (k : ℝ) =
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ) * (k : ℝ) ^ 2 := by ring
  simp_rw [he] at hs
  have hint : Integrable (fun k : ℕ => (k : ℝ) ^ 2) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hs.summable
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using hs.tsum_eq

end Rhone.Probability
