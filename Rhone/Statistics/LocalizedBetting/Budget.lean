/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LocalizedBetting.Concentration

/-! # Exact exponential certificate for the localization sample budget -/

@[expose] public section

namespace Rhone.Statistics.LocalizedBetting

theorem exp_eight_lower : (2500 : ℝ) ≤ Real.exp 8 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 12
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem localization_budget {N : ℕ} (hN : 72000000000 ≤ N) :
    6 * Real.exp (-9 * (N : ℝ) * (1 / 100000) ^ 2 / 8) ≤ (3 : ℝ) / 1250 := by
  have hn : (72000000000 : ℝ) ≤ N := by exact_mod_cast hN
  have he : -9 * (N : ℝ) * (1 / 100000) ^ 2 / 8 ≤ -8 := by linarith
  have h := Real.exp_le_exp.mpr he
  rw [Real.exp_neg] at h
  have hi : (Real.exp 8)⁻¹ ≤ (2500 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) exp_eight_lower
  linarith

end Rhone.Statistics.LocalizedBetting
