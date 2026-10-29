/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Ring

/-! # Stirling numbers of the second kind -/

@[expose] public section

namespace Rhone.Combinatorics

open Finset

theorem stirlingSecond_recurrence (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1) =
      (k + 1) * Nat.stirlingSecond n (k + 1) + Nat.stirlingSecond n k :=
  Nat.stirlingSecond_succ_succ n k

theorem stirlingSecond_zero_zero : Nat.stirlingSecond 0 0 = 1 := Nat.stirlingSecond_zero

theorem stirlingSecond_zero_succ (k : ℕ) : Nat.stirlingSecond 0 (k + 1) = 0 :=
  Nat.stirlingSecond_zero_succ k

theorem stirlingSecond_succ_zero (n : ℕ) : Nat.stirlingSecond (n + 1) 0 = 0 :=
  Nat.stirlingSecond_succ_zero n

theorem stirlingSecond_eq_zero_of_lt {n k : ℕ} (h : n < k) : Nat.stirlingSecond n k = 0 :=
  Nat.stirlingSecond_eq_zero_of_lt h

theorem stirlingSecond_self (n : ℕ) : Nat.stirlingSecond n n = 1 := Nat.stirlingSecond_self n

theorem stirlingSecond_succ_one (n : ℕ) : Nat.stirlingSecond (n + 1) 1 = 1 :=
  Nat.stirlingSecond_one_right n

theorem stirlingSecond_succ_self_left (n : ℕ) :
    Nat.stirlingSecond (n + 1) n = (n + 1).choose 2 := Nat.stirlingSecond_succ_self_left n

theorem pow_eq_sum_stirlingSecond_mul_fallingProd {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    x ^ n = ∑ k ∈ range (n + 1), (Nat.stirlingSecond n k : R) * ∏ i ∈ range k, (x - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hF : ∀ k : ℕ, x * ∏ i ∈ range k, (x - i) =
        ∏ i ∈ range (k + 1), (x - i) + k * ∏ i ∈ range k, (x - i) := by
      intro k
      rw [prod_range_succ]
      ring
    have hterm : ∀ k : ℕ, x * ((Nat.stirlingSecond n k : R) * ∏ i ∈ range k, (x - i)) =
        (Nat.stirlingSecond n k : R) * ∏ i ∈ range (k + 1), (x - i) +
          ((Nat.stirlingSecond n k : R) * k) * ∏ i ∈ range k, (x - i) := by
      intro k
      rw [mul_left_comm, hF]
      ring
    have hshift : ∑ k ∈ range (n + 1), ((Nat.stirlingSecond n k : R) * k) *
          ∏ i ∈ range k, (x - i) =
        ∑ k ∈ range (n + 1), ((k : R) + 1) * (Nat.stirlingSecond n (k + 1) : R) *
          ∏ i ∈ range (k + 1), (x - i) := by
      rw [sum_range_succ' (fun k => ((Nat.stirlingSecond n k : R) * k) *
          ∏ i ∈ range k, (x - i)) n,
        sum_range_succ (fun k => ((k : R) + 1) * (Nat.stirlingSecond n (k + 1) : R) *
          ∏ i ∈ range (k + 1), (x - i)) n,
        Nat.stirlingSecond_eq_zero_of_lt n.lt_add_one]
      simp [mul_comm]
    rw [pow_succ', ih, mul_sum]
    simp only [hterm]
    rw [sum_add_distrib, hshift, sum_range_succ' _ (n + 1)]
    simp only [Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_succ_zero, Nat.cast_add,
      Nat.cast_mul, Nat.cast_zero, zero_mul, add_zero, Nat.cast_succ, add_mul, sum_add_distrib]
    simp only [Finset.sum_const_zero, zero_add]
    rw [add_comm, add_assoc]

theorem sum_stirlingSecond_descFactorial (x n : ℕ) :
    ∑ m ∈ range (n + 1), Nat.stirlingSecond n m * x.descFactorial m = x ^ n :=
  (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial x n).symm

end Rhone.Combinatorics
