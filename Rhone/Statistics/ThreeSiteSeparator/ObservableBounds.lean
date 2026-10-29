/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.ObservableAlgebra
public import Mathlib.Tactic.Linarith

/-! # Uniform bounds for the explicit finite-alphabet allele scores -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.ThreeSiteSeparator

lemma pairScore_abs_le_one {K : ℕ} (hK : 2 ≤ K) (a b : Fin K) :
    |pairScore K a b| ≤ 1 := by
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hd : 0 < (K : ℝ) - 1 := by linarith
  unfold pairScore
  by_cases hab : a = b
  · simp [hab, ne_of_gt hd]
  · simp only [hab, ite_false, mul_zero, zero_sub, abs_div, abs_neg, abs_one,
      abs_of_pos hd]
    exact (div_le_one hd).mpr (by linarith)

lemma tripleScore_cases {K : ℕ} (hK : 3 ≤ K) (a b c : Fin K) :
    tripleScore K a b c =
      if a = b ∧ a = c then 1 else
      if a = b ∨ a = c ∨ b = c then -1/((K : ℝ) - 1) else
        2/(((K : ℝ) - 1)*(K - 2)) := by
  have hk : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : (K : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (K : ℝ) - 2 ≠ 0 := by linarith
  unfold tripleScore
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · simp [hac]
      field_simp
      ring
    · simp [hac]
      field_simp
      ring
  · by_cases hac : a = c
    · subst c
      simp [hab, Ne.symm hab]
      field_simp
      ring
    · by_cases hbc : b = c
      · simp [hac, hbc]
        field_simp
        ring
      · simp [hab, hac, hbc]

lemma tripleScore_abs_le_one {K : ℕ} (hK : 3 ≤ K) (a b c : Fin K) :
    |tripleScore K a b c| ≤ 1 := by
  have hk : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : 0 < (K : ℝ) - 1 := by linarith
  have h2 : 0 < (K : ℝ) - 2 := by linarith
  have hd : 0 < ((K : ℝ) - 1)*(K - 2) := mul_pos h1 h2
  rw [tripleScore_cases hK]
  split_ifs
  · norm_num
  · rw [abs_div, abs_neg, abs_one, abs_of_pos h1]
    exact (div_le_one h1).mpr (by linarith)
  · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hd]
    apply (div_le_one hd).mpr
    nlinarith [sq_nonneg ((K : ℝ) - 3)]

end Rhone.Statistics.ThreeSiteSeparator
