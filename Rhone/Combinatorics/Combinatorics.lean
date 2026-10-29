/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Rising factorials, Stirling numbers of the first kind, harmonic numbers

Source: knuth1997, sec. 1.2.5, eq. (19), p. 50, sec. 1.2.6, eq. (44), p. 67, p. 71, sec. 1.2.7, eq.
(1), p. 75. -/

@[expose] public section

namespace Rhone.Combinatorics

open Finset Polynomial

theorem sum_inv_mul_pred (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 2 n, (1 : ℚ) / (k * (k - 1)) = 1 - 1 / n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have h1 : (n : ℚ) ≠ 0 := by positivity
    push_cast
    rw [show ((n : ℚ) + 1 - 1) = n by ring]
    field_simp
    ring

theorem sum_inv_pred (n : ℕ) :
    ∑ k ∈ Icc 2 n, (1 : ℚ) / (k - 1) = harmonic (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h | h
    · obtain rfl : n = 0 := by omega
      simp
    · rw [Finset.sum_Icc_succ_top (by omega), ih]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [harmonic_succ]

theorem ascPochhammer_eq_sum_stirlingFirst (R : Type*) [CommSemiring R] (n : ℕ) :
    ascPochhammer R n =
      ∑ k ∈ range (n + 1), C (Nat.stirlingFirst n k : R) * X ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : (n : R[X]) * (C (Nat.stirlingFirst n 0 : R) * X ^ 0) = 0 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp
    have key : ∑ k ∈ range (n + 1), (n : R[X]) * (C (Nat.stirlingFirst n k : R) * X ^ k) =
        ∑ k ∈ range (n + 1), (n : R[X]) * (C (Nat.stirlingFirst n (k + 1) : R) * X ^ (k + 1)) := by
      have := Finset.sum_range_succ' (fun k => (n : R[X]) *
        (C (Nat.stirlingFirst n k : R) * X ^ k)) (n + 1)
      rw [Finset.sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n), h0] at this
      simpa using this
    have e1 : ∀ k, C (Nat.stirlingFirst (n + 1) (k + 1) : R) * X ^ (k + 1) =
        (n : R[X]) * (C (Nat.stirlingFirst n (k + 1) : R) * X ^ (k + 1))
          + C (Nat.stirlingFirst n k : R) * X ^ (k + 1) := by
      intro k
      rw [Nat.stirlingFirst_succ_succ]
      simp only [Nat.cast_add, Nat.cast_mul, map_add, map_mul, map_natCast]
      ring
    have h3 : ∀ k ∈ range (n + 1), C (Nat.stirlingFirst n k : R) * X ^ k * (X + (n : R[X])) =
        C (Nat.stirlingFirst n k : R) * X ^ (k + 1)
          + (n : R[X]) * (C (Nat.stirlingFirst n k : R) * X ^ k) := by
      intro k _
      ring
    rw [ascPochhammer_succ_right, ih, Finset.sum_mul, Finset.sum_range_succ' _ (n + 1),
      Finset.sum_congr rfl h3, Finset.sum_add_distrib, key]
    simp only [e1, Finset.sum_add_distrib, Nat.stirlingFirst_succ_zero]
    simp [add_comm]

theorem ascPochhammer_eval_eq_sum_stirlingFirst {R : Type*} [CommSemiring R] (n : ℕ) (x : R) :
    (ascPochhammer R n).eval x = ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : R) * x ^ k := by
  rw [ascPochhammer_eq_sum_stirlingFirst, eval_finsetSum]
  simp

theorem sum_stirlingFirst_eq_factorial (n : ℕ) :
    ∑ k ∈ range (n + 1), Nat.stirlingFirst n k = n.factorial := by
  have h := ascPochhammer_eval_eq_sum_stirlingFirst (R := ℕ) n 1
  simp only [one_pow, mul_one, Nat.cast_id] at h
  rw [← h, ascPochhammer_nat_eq_ascFactorial]
  simp

theorem harmonic_eq_sum_Icc_inv (n : ℕ) : harmonic n = ∑ i ∈ Icc 1 n, (1 : ℚ) / i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    simp [one_div]

theorem zero_lt_harmonic {n : ℕ} (hn : n ≠ 0) : 0 < harmonic n := by
  unfold harmonic
  exact Finset.sum_pos (fun i _ => inv_pos.2 (by exact_mod_cast Nat.succ_pos i))
    (Finset.nonempty_range_iff.2 hn)

theorem sum_Icc_sub (c : ℚ) (m : ℕ) :
    ∑ i ∈ Icc 1 m, (c - i) = m * c - m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

end Rhone.Combinatorics
