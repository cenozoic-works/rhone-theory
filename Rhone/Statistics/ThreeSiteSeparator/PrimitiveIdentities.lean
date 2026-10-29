/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.WeightedPrimitive

/-! # Exact integration-by-parts identities for the CDF energy decomposition -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma weighted_integral_identity (r n : ℕ) {H : ℝ → ℝ} (hH : Continuous H) :
    ((n : ℝ) + 1) * (∫ x in (0 : ℝ)..1, x^n * weightedPrimitive r H x) =
      weightedPrimitive r H 1 - ∫ x in (0 : ℝ)..1, x^(n + r + 1) * H x := by
  have hd (x : ℝ) : HasDerivAt (fun t => t^(n + 1) * weightedPrimitive r H t)
      (((n : ℝ) + 1) * (x^n * weightedPrimitive r H x) + x^(n + r + 1) * H x) x := by
    convert! (hasDerivAt_pow (n + 1) x).mul (weightedPrimitive_deriv r hH x) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_add, pow_one]
    ring
  have hc1 : Continuous (fun x : ℝ => ((n : ℝ) + 1) *
      (x^n * weightedPrimitive r H x)) := by fun_prop
  have hc2 : Continuous (fun x : ℝ => x^(n + r + 1) * H x) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((hc1.add hc2).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul] at he
  simp only [one_pow, one_mul, weightedPrimitive_zero, mul_zero, sub_zero] at he
  linarith

lemma cross_primitive_identity (r s : ℕ) {H : ℝ → ℝ} (hH : Continuous H) :
    (∫ x in (0 : ℝ)..1, x^r * H x * weightedPrimitive s H x) +
      (∫ x in (0 : ℝ)..1, x^s * H x * weightedPrimitive r H x) =
      weightedPrimitive r H 1 * weightedPrimitive s H 1 := by
  have hd (x : ℝ) : HasDerivAt
      (fun t => weightedPrimitive r H t * weightedPrimitive s H t)
      (x^r * H x * weightedPrimitive s H x + x^s * H x * weightedPrimitive r H x) x := by
    convert! (weightedPrimitive_deriv r hH x).mul (weightedPrimitive_deriv s hH x) using 1
    ring
  have hc1 : Continuous (fun x : ℝ => x^r * H x * weightedPrimitive s H x) := by fun_prop
  have hc2 : Continuous (fun x : ℝ => x^s * H x * weightedPrimitive r H x) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((hc1.add hc2).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)] at he
  simpa only [weightedPrimitive_zero, zero_mul, sub_zero] using he

lemma square_primitive_identity (r : ℕ) {H : ℝ → ℝ} (hH : Continuous H) :
    2 * (∫ x in (0 : ℝ)..1, x^r * H x * weightedPrimitive r H x) =
      (weightedPrimitive r H 1)^2 := by
  have he := cross_primitive_identity r r hH
  nlinarith

lemma weighted_square_identity {H : ℝ → ℝ} (hH : Continuous H) :
    (∫ x in (0 : ℝ)..1, x^5 * H x * weightedPrimitive 1 H x) =
      (weightedPrimitive 1 H 1)^2 / 2 -
        2 * ∫ x in (0 : ℝ)..1, x^3 * (weightedPrimitive 1 H x)^2 := by
  have hd (x : ℝ) : HasDerivAt (fun t => t^4 * (weightedPrimitive 1 H t)^2)
      (4 * (x^3 * (weightedPrimitive 1 H x)^2) +
        2 * (x^5 * H x * weightedPrimitive 1 H x)) x := by
    convert! (hasDerivAt_pow 4 x).mul ((weightedPrimitive_deriv 1 hH x).pow 2) using 1
    norm_num
    ring
  have hc1 : Continuous (fun x : ℝ => 4 * (x^3 * (weightedPrimitive 1 H x)^2)) := by fun_prop
  have hc2 : Continuous (fun x : ℝ => 2 * (x^5 * H x * weightedPrimitive 1 H x)) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((hc1.add hc2).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  simp only [one_pow, one_mul, weightedPrimitive_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero] at he
  linarith

end Rhone.Statistics.ThreeSiteSeparator
