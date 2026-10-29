/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.Watterson

/-!
# Algebraic identities for Tajima's coefficients

Source: tajima1989, p. 585, eq. (3)–(4), (8)–(9), p. 588, eq. (30)–(37). -/

@[expose] public section
namespace Rhone.Statistics
open Finset Rhone.Combinatorics

theorem tajimaA1_succ {n : ℕ} (hn : 1 ≤ n) :
    tajimaA1 (n + 1) = tajimaA1 n + 1 / (n : ℚ) := by
  unfold tajimaA1
  rw [show n + 1 - 1 = (n - 1) + 1 by omega, harmonic_succ,
    show n - 1 + 1 = n by omega, one_div]

theorem tajimaA2_succ {n : ℕ} (hn : 1 ≤ n) :
    tajimaA2 (n + 1) = tajimaA2 n + 1 / (n : ℚ) ^ 2 := by
  unfold tajimaA2
  rw [show n + 1 - 1 = (n - 1) + 1 by omega,
    Finset.sum_Icc_succ_top (by omega), show n - 1 + 1 = n by omega]

theorem tajimaB1_mul {n : ℕ} (hn : 2 ≤ n) :
    tajimaB1 n * (3 * ((n : ℚ) - 1)) = (n : ℚ) + 1 := by
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hden : (3 : ℚ) * ((n : ℚ) - 1) ≠ 0 := by nlinarith
  exact div_mul_cancel₀ _ hden

theorem tajimaB2_mul {n : ℕ} (hn : 2 ≤ n) :
    tajimaB2 n * (9 * (n : ℚ) * ((n : ℚ) - 1)) =
      2 * ((n : ℚ) ^ 2 + n + 3) := by
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hden : (9 : ℚ) * n * ((n : ℚ) - 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by linarith)) (by linarith)
  exact div_mul_cancel₀ _ hden

theorem tajimaE1_mul {n : ℕ} (hn : 2 ≤ n) :
    tajimaE1 n * tajimaA1 n = tajimaC1 n := by
  have hpos : 0 < tajimaA1 n := zero_lt_harmonic (by omega)
  exact div_mul_cancel₀ _ hpos.ne'

theorem tajimaE2_mul {n : ℕ} (hn : 2 ≤ n) :
    tajimaE2 n * (tajimaA1 n ^ 2 + tajimaA2 n) = tajimaC2 n := by
  have ha1 : 0 < tajimaA1 n := zero_lt_harmonic (by omega)
  have ha2 : 0 ≤ tajimaA2 n := by
    unfold tajimaA2
    exact Finset.sum_nonneg fun _ _ => div_nonneg (by norm_num) (sq_nonneg _)
  have hden : tajimaA1 n ^ 2 + tajimaA2 n ≠ 0 := by nlinarith
  exact div_mul_cancel₀ _ hden

theorem tajimaC1_two : tajimaC1 2 = 0 := by
  norm_num [tajimaC1, tajimaB1, tajimaA1, harmonic_succ, harmonic_zero]

theorem tajimaC2_two : tajimaC2 2 = 0 := by
  norm_num [tajimaC2, tajimaB2, tajimaA1, tajimaA2, harmonic_succ,
    harmonic_zero, Finset.sum_Icc_succ_top]

theorem tajimaE1_two : tajimaE1 2 = 0 := by simp [tajimaE1, tajimaC1_two]

theorem tajimaE2_two : tajimaE2 2 = 0 := by simp [tajimaE2, tajimaC2_two]

theorem tajimaC1_three : tajimaC1 3 = 0 := by
  norm_num [tajimaC1, tajimaB1, tajimaA1, harmonic_succ, harmonic_zero]

theorem tajimaC2_three : tajimaC2 3 = 0 := by
  norm_num [tajimaC2, tajimaB2, tajimaA1, tajimaA2, harmonic_succ,
    harmonic_zero, Finset.sum_Icc_succ_top]

theorem tajimaE1_three : tajimaE1 3 = 0 := by simp [tajimaE1, tajimaC1_three]

theorem tajimaE2_three : tajimaE2 3 = 0 := by simp [tajimaE2, tajimaC2_three]

end Rhone.Statistics
