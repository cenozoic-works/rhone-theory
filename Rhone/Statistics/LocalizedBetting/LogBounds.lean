/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.VarianceAwarePairBetting.LogBounds

/-! # Small-increment bounds for the concrete product calibration -/

@[expose] public section

namespace Rhone.Statistics.LocalizedBetting

theorem log_lower {x : ℝ} (hx : |x| ≤ 1 / 100) :
    x - 511 / 1000 * x ^ 2 ≤ Real.log (1 + x) := by
  have hab : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hab 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
  norm_num at h
  have hd : 0 < 1 - |x| := by linarith
  have hr : |x| ^ 3 / (1 - |x|) ≤ 11 / 1000 * x ^ 2 := by
    apply (div_le_iff₀ hd).mpr
    have hs : |x| ^ 2 = x ^ 2 := sq_abs x
    have hp := mul_le_mul_of_nonneg_left hx (sq_nonneg |x|)
    nlinarith [abs_nonneg x]
  have hl := (abs_le.mp h).1
  linarith

theorem abs_log_upper {x : ℝ} (hx : |x| ≤ 1 / 100) :
    |Real.log (1 + x)| ≤ 100 / 99 * |x| := by
  have hab : |(-x)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hab 0
  norm_num [abs_neg, sub_neg_eq_add] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - |x|)).mpr
  have hp := mul_le_mul_of_nonneg_left hx (abs_nonneg x)
  nlinarith [abs_nonneg x]

theorem log_second_upper {x : ℝ} (hx : |x| ≤ 1 / 100) :
    Real.log (1 + x) ^ 2 ≤ 1021 / 1000 * x ^ 2 := by
  have h := abs_log_upper hx
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  nlinarith [sq_abs (Real.log (1 + x)), sq_abs x, sq_nonneg x]

end Rhone.Statistics.LocalizedBetting
