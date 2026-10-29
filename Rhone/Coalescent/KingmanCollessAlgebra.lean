/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
/-!
# Finite root-imbalance sums used to solve the Colless expectation recurrence

Source: cardona2013balance, §7. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: cardona2013balance, §7. -/
noncomputable def collessToll (n : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 n, ((max k (n - k) - min k (n - k) : ℕ) : ℝ)
/-- Source: cardona2013balance, §7. -/
theorem collessToll_succ (n : ℕ) (hn : 1 ≤ n) :
    collessToll (n + 1) = collessToll n + 2 * (n / 2 : ℕ) := by
  have hdiff : ∀ k ∈ Ico 1 n,
      ((max k (n + 1 - k) - min k (n + 1 - k) : ℕ) : ℝ) =
      ((max k (n - k) - min k (n - k) : ℕ) : ℝ) +
        (if 2 * k ≤ n then 1 else -1) := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := mem_Ico.mp hk
    by_cases h : 2 * k ≤ n
    · rw [ite_eq_left h, max_eq_right (by omega : k ≤ n - k),
        min_eq_left (by omega : k ≤ n - k),
        max_eq_right (by omega : k ≤ n + 1 - k), min_eq_left (by omega : k ≤ n + 1 - k)]
      have he : n + 1 - k - k = (n - k - k) + 1 := by omega
      rw [he, Nat.cast_add, Nat.cast_one]
    · rw [ite_eq_right h, max_eq_left (by omega : n - k ≤ k),
        min_eq_right (by omega : n - k ≤ k),
        max_eq_left (by omega : n + 1 - k ≤ k), min_eq_right (by omega : n + 1 - k ≤ k)]
      have he : k - (n - k) = (k - (n + 1 - k)) + 1 := by omega
      have heR := congrArg (fun z : ℕ => (z : ℝ)) he
      simp only [Nat.cast_add, Nat.cast_one] at heR
      linarith
  have hf : (Ico 1 n).filter (fun k => 2 * k ≤ n) = Ico 1 (n / 2 + 1) := by
    ext k
    simp only [mem_filter, mem_Ico]
    omega
  have hcount : (∑ k ∈ Ico 1 n, if 2 * k ≤ n then (1 : ℝ) else 0) = (n / 2 : ℕ) := by
    rw [← sum_filter, hf, sum_const, nsmul_eq_mul, Nat.card_Ico]
    simp
  have hsign : (∑ k ∈ Ico 1 n, if 2 * k ≤ n then (1 : ℝ) else -1) =
      2 * (n / 2 : ℕ) - (n - 1 : ℕ) := by
    have ht : ∀ k ∈ Ico 1 n, (if 2 * k ≤ n then (1 : ℝ) else -1) =
        2 * (if 2 * k ≤ n then (1 : ℝ) else 0) - 1 := by
      intro k hk
      split_ifs <;> norm_num
    rw [sum_congr rfl ht, sum_sub_distrib, ← mul_sum, hcount,
      sum_const, nsmul_eq_mul, Nat.card_Ico, mul_one]
  unfold collessToll
  rw [sum_Ico_succ_top hn, sum_congr rfl hdiff, sum_add_distrib, hsign]
  have hlast : max n (n + 1 - n) - min n (n + 1 - n) = n - 1 := by
    simp only [Nat.add_sub_cancel_left]
    rw [max_eq_left hn, min_eq_right hn]
  rw [hlast]
  ring
/-- Source: cardona2013balance, §7. -/
theorem colless_closed_succ (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ) * (((harmonic ((n + 1) / 2) : ℚ) : ℝ)) - 2 * ((n + 1) / 2 : ℕ) =
      (((n + 1 : ℕ) : ℝ) / n) *
        ((n : ℝ) * (((harmonic (n / 2) : ℚ) : ℝ)) - 2 * (n / 2 : ℕ)) +
        2 * (n / 2 : ℕ) / n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  by_cases h : n % 2 = 0
  · have he : (n + 1) / 2 = n / 2 := by omega
    have hn2 : n = 2 * (n / 2) := by omega
    have hnR : (n : ℝ) = 2 * (n / 2 : ℕ) := by exact_mod_cast hn2
    rw [he]
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    nlinarith
  · have he : (n + 1) / 2 = n / 2 + 1 := by omega
    have hn2 : n + 1 = 2 * (n / 2 + 1) := by omega
    have hnR : (n : ℝ) + 1 = 2 * ((n / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast hn2
    have hm0 : ((n / 2 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [he, harmonic_succ]
    simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Rat.cast_one,
      Nat.cast_add, Nat.cast_one]
    have hcancel : ((n : ℝ) + 1) * (((n / 2 : ℕ) : ℝ) + 1)⁻¹ = 2 := by
      have hh : (n : ℝ) + 1 = 2 * (((n / 2 : ℕ) : ℝ) + 1) := by linarith
      rw [hh, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hm0), mul_one]
    have hexpand : ((n : ℝ) + 1) *
        ((((harmonic (n / 2) : ℚ) : ℝ)) + (((n / 2 : ℕ) : ℝ) + 1)⁻¹) =
        ((n : ℝ) + 1) * (((harmonic (n / 2) : ℚ) : ℝ)) + 2 := by
      rw [mul_add, hcancel]
    rw [hexpand]
    field_simp
    ring
end Rhone.Coalescent
