/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanCollessRecurrence
public import Rhone.Coalescent.KingmanCollessAlgebra
/-!
# Exact Colless expectation for labelled Kingman genealogy histories

Source: cardona2013balance, §7; kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: cardona2013balance, §7. -/
theorem colless_expected_normalized (n : ℕ) (hn : 1 ≤ n) :
    ((n - 1 : ℕ) : ℝ) * collessExpected n =
      2 * (∑ k ∈ Ico 1 n, collessExpected k) + collessToll n := by
  by_cases h1 : n = 1
  · subst n
    simp [collessToll]
  · have hn2 : 2 ≤ n := by omega
    have hm : (∑ k ∈ Ico 1 n, collessExpected (n - k)) =
        ∑ k ∈ Ico 1 n, collessExpected k := by
      simpa using sum_Ico_reflect collessExpected 1 (m := n) (n := n) (by omega)
    have hs : (∑ k ∈ Ico 1 n, (collessExpected k + collessExpected (n - k) +
        ((max k (n - k) - min k (n - k) : ℕ) : ℝ))) =
        2 * (∑ k ∈ Ico 1 n, collessExpected k) + collessToll n := by
      rw [sum_add_distrib, sum_add_distrib, hm]
      unfold collessToll
      ring
    have hh := kingman_colless_recurrence n hn2
    rw [hs] at hh
    have hden : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp at hh
    nlinarith
/-- Source: cardona2013balance, §7. -/
theorem colless_expected_succ (n : ℕ) (hn : 1 ≤ n) :
    collessExpected (n + 1) = (((n + 1 : ℕ) : ℝ) / n) * collessExpected n +
      2 * (n / 2 : ℕ) / n := by
  have hp := colless_expected_normalized (n + 1) (by omega)
  rw [Nat.add_sub_cancel, sum_Ico_succ_top hn, collessToll_succ n hn] at hp
  have hm := colless_expected_normalized n hn
  rw [Nat.cast_sub hn, Nat.cast_one] at hm
  have hstep : (n : ℝ) * collessExpected (n + 1) =
      ((n : ℝ) + 1) * collessExpected n + 2 * (n / 2 : ℕ) := by
    nlinarith [hp, hm]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  nlinarith [hstep]
/--
Source: heard1992, eq. (2), p. 1820, Appendix, pp. 1824–1826; fischer_etal2023_tree_balance, sec.
9.6; cardona2013balance, §7. -/
theorem kingman_colless_expectation (n : ℕ) (hn : 1 ≤ n) :
    Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => (treeColless G : ℝ)) =
      (n : ℝ) * (((harmonic (n / 2) : ℚ) : ℝ)) - 2 * (n / 2 : ℕ) := by
  change collessExpected n = _
  induction n, hn using Nat.le_induction with
  | base =>
    have hbase : collessExpected 1 = 0 := by
      simpa only [collessExpected, Nat.sub_self] using kingman_colless_expectation_one
    rw [hbase]
    norm_num [harmonic]
  | succ n hn ih =>
    rw [colless_expected_succ n hn, ih]
    exact (colless_closed_succ n hn).symm
end Rhone.Coalescent
