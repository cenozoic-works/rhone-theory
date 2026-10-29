/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Choose.Cast
public import Rhone.Combinatorics.Combinatorics

/-!
# Kingman coalescent: rates, holding times, tree height, and tree length

Source: kingman1982, eq. (1.7), (1.12)–(1.13); hudson1990, eq. (5)–(6), pp. 8–9; tavare1984, eq.
(3.8), p. 126, sec. 6, p. 132; bryant_etal2011_exact_likelihoods, sec. 2. -/

@[expose] public section

namespace Rhone.Coalescent

open Finset Rhone.Combinatorics

def coalRate (k : ℕ) : ℚ := k * (k - 1) / 2

def holdingTime (k : ℕ) : ℚ := 1 / coalRate k

def expTMRCA (n : ℕ) : ℚ := ∑ k ∈ Icc 2 n, holdingTime k

def expLength (n : ℕ) : ℚ := ∑ k ∈ Icc 2 n, k * holdingTime k

def varTMRCA (n : ℕ) : ℚ := ∑ k ∈ Icc 2 n, holdingTime k ^ 2

def varLength (n : ℕ) : ℚ := ∑ k ∈ Icc 2 n, ((k : ℚ) * holdingTime k) ^ 2

theorem coalRate_eq_choose (k : ℕ) : coalRate k = (k.choose 2 : ℚ) := by
  rw [Nat.cast_choose_two ℚ]
  rfl

theorem coalRate_pos {k : ℕ} (hk : 2 ≤ k) : 0 < coalRate k := by
  have : (2 : ℚ) ≤ k := by exact_mod_cast hk
  unfold coalRate
  nlinarith

theorem holdingTime_eq {k : ℕ} (hk : 2 ≤ k) : holdingTime k = 2 / (k * (k - 1)) := by
  have h : (2 : ℚ) ≤ k := by exact_mod_cast hk
  unfold holdingTime coalRate
  rw [one_div_div]

theorem expTMRCA_eq {n : ℕ} (hn : 1 ≤ n) : expTMRCA n = 2 * (1 - 1 / n) := by
  unfold expTMRCA
  rw [Finset.sum_congr rfl fun k hk => holdingTime_eq (mem_Icc.1 hk).1]
  have := sum_inv_mul_pred n hn
  calc ∑ k ∈ Icc 2 n, (2 : ℚ) / (k * (k - 1))
      = 2 * ∑ k ∈ Icc 2 n, (1 : ℚ) / (k * (k - 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 2 * (1 - 1 / n) := by rw [this]

theorem expTMRCA_two : expTMRCA 2 = 1 := by
  rw [expTMRCA_eq (by norm_num)]
  norm_num

theorem expTMRCA_lt_two {n : ℕ} (hn : 1 ≤ n) : expTMRCA n < 2 := by
  rw [expTMRCA_eq hn]
  have hpos : (0 : ℚ) < n := by exact_mod_cast hn
  have : (0 : ℚ) < 1 / n := one_div_pos.2 hpos
  linarith

theorem expLength_eq (n : ℕ) : expLength n = 2 * harmonic (n - 1) := by
  unfold expLength
  rw [← sum_inv_pred n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h : (2 : ℚ) ≤ k := by exact_mod_cast (mem_Icc.1 hk).1
  rw [holdingTime_eq (mem_Icc.1 hk).1]
  have : (k : ℚ) - 1 ≠ 0 := by linarith
  field_simp

theorem varLength_eq (n : ℕ) :
    varLength n = 4 * ∑ k ∈ Icc 1 (n - 1), (1 : ℚ) / (k : ℚ) ^ 2 := by
  have shift : ∀ m : ℕ, varLength (m + 1) = 4 * ∑ k ∈ Icc 1 m, (1 : ℚ) / (k : ℚ) ^ 2 := by
    intro m
    induction m with
    | zero => simp [varLength]
    | succ m ih =>
      unfold varLength at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega),
        holdingTime_eq (by omega)]
      push_cast
      have : (m : ℚ) + 1 ≠ 0 := by positivity
      field_simp
      ring
  rcases n with _ | m
  · simp [varLength]
  · simpa using shift m

theorem varTMRCA_eq (n : ℕ) :
    varTMRCA n = ∑ k ∈ Icc 2 n, (2 / ((k : ℚ) * (k - 1))) ^ 2 := by
  unfold varTMRCA
  exact Finset.sum_congr rfl fun k hk => by rw [holdingTime_eq (mem_Icc.1 hk).1]

end Rhone.Coalescent
