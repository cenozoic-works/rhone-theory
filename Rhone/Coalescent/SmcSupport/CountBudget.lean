/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-! # A nonnegative count budget for absorption of the contact process -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport

noncomputable def countSlope (C : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 3
  | k + 1, n => (C * countSlope C k (n + 1) + C + (n : ℝ)) / (n : ℝ)

noncomputable def countBudget (C : ℝ) (M n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, countSlope C (M - (j + 1)) (j + 1)

theorem countSlope_ge_one (C : ℝ) (hC : 0 ≤ C) (k n : ℕ) (hn : 0 < n) :
    1 ≤ countSlope C k n := by
  induction k generalizing n with
  | zero => norm_num [countSlope]
  | succ k ih =>
    have hi := ih (n + 1) (by omega)
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [countSlope, le_div_iff₀ hn']
    nlinarith [mul_nonneg hC (le_trans zero_le_one hi)]

theorem countBudget_nonneg (C : ℝ) (hC : 0 ≤ C) (M n : ℕ) :
    0 ≤ countBudget C M n := by
  apply Finset.sum_nonneg
  intro j _
  exact le_trans zero_le_one (countSlope_ge_one C hC _ _ (by omega))

theorem countBudget_monotone (C : ℝ) (hC : 0 ≤ C) (M : ℕ) :
    Monotone (countBudget C M) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold countBudget
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right
    (le_trans zero_le_one (countSlope_ge_one C hC _ _ (by omega)))

theorem countSlope_balance (C : ℝ) (hC : 0 ≤ C) (M n : ℕ)
    (hM : 2 * C ≤ (M : ℝ)) (hn : 0 < n) :
    C + (n : ℝ) ≤ (n : ℝ) * countSlope C (M - n) n -
      C * countSlope C (M - (n + 1)) (n + 1) := by
  have _ := hC
  by_cases hlt : n < M
  · have he : M - n = M - (n + 1) + 1 := by omega
    rw [he, countSlope]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact le_of_eq (by field_simp; ring)
  · have he : M - n = 0 := by omega
    have he' : M - (n + 1) = 0 := by omega
    rw [he, he', countSlope, countSlope]
    have hle : (M : ℝ) ≤ n := Nat.cast_le.mpr (by omega)
    nlinarith

theorem countBudget_step_le (C : ℝ) (hC : 0 ≤ C) (M n : ℕ)
    (hM : 2 * C ≤ (M : ℝ)) (hn : 0 < n) (p : ℝ)
    (hp0 : 0 ≤ p) (hp : p ≤ C / (C + (n : ℝ))) :
    p * countBudget C M (n + 1) + (1 - p) * countBudget C M (n - 1) ≤
      countBudget C M n - 1 := by
  have _ := hp0
  have hd : (0 : ℝ) < C + n := by exact add_pos_of_nonneg_of_pos hC (Nat.cast_pos.mpr hn)
  have hbal := countSlope_balance C hC M n hM hn
  have hsucc : countBudget C M (n + 1) = countBudget C M n +
      countSlope C (M - (n + 1)) (n + 1) := by
    exact Finset.sum_range_succ _ _
  have hpred : countBudget C M n = countBudget C M (n - 1) +
      countSlope C (M - n) n := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [countBudget, Finset.sum_range_succ]
    simp only [← he]
    rfl
  have hinc : 0 ≤ countBudget C M (n + 1) - countBudget C M (n - 1) :=
    sub_nonneg.mpr (countBudget_monotone C hC M (by omega))
  have hmix := mul_le_mul_of_nonneg_right hp hinc
  have heq : C / (C + (n : ℝ)) * countBudget C M (n + 1) +
      (1 - C / (C + (n : ℝ))) * countBudget C M (n - 1) =
      countBudget C M n +
        (C * countSlope C (M - (n + 1)) (n + 1) -
          (n : ℝ) * countSlope C (M - n) n) / (C + (n : ℝ)) := by
    rw [hsucc, hpred]
    field_simp
    ring
  have he : C / (C + (n : ℝ)) * countBudget C M (n + 1) +
      (1 - C / (C + (n : ℝ))) * countBudget C M (n - 1) ≤
      countBudget C M n - 1 := by
    rw [heq]
    have hterm : (C * countSlope C (M - (n + 1)) (n + 1) -
        (n : ℝ) * countSlope C (M - n) n) / (C + (n : ℝ)) ≤ -1 := by
      apply (div_le_iff₀ hd).mpr
      linarith
    linarith
  nlinarith

end Rhone.Coalescent.SmcSupport
