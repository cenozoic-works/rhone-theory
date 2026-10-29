/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Rhone.Combinatorics.CycleIndex

/-!
# The Ewens sampling formula

Source: ewens1972, eq. (23), (29)–(30), eq. (A3), pp. 95, 100–102, 107; tavare2004, sec. 3.5, Thm
3.1, eq. (3.5.3), p. 36. -/

@[expose] public section

namespace Rhone.Probability

open Finset Polynomial Rhone.Combinatorics

variable {F : Type*} [Field F]

noncomputable def esf (θ : F) {n : ℕ} (p : Nat.Partition n) : F :=
  (n.factorial : F) * θ ^ p.parts.card * partWeight F p.parts / (ascPochhammer F n).eval θ

theorem sum_partWeight_mul_pow [CharZero F] (θ : F) (n : ℕ) :
    ∑ p : Nat.Partition n, partWeight F p.parts * θ ^ p.parts.card =
      (n.factorial : F)⁻¹ * (ascPochhammer F n).eval θ := by
  have h := congrArg (Polynomial.eval θ) (cycleIndex_eq (F := F) n)
  rw [cycleIndex, eval_finsetSum] at h
  simpa using h

theorem esf_eq_prod (θ : F) {n : ℕ} (p : Nat.Partition n) :
    esf θ p = (n.factorial : F) / (ascPochhammer F n).eval θ *
      ∏ j ∈ Icc 1 n, (θ / j) ^ p.parts.count j / (p.parts.count j).factorial := by
  classical
  have hsub : p.parts.toFinset ⊆ Icc 1 n := fun j hj => by
    have hj' := Multiset.mem_toFinset.1 hj
    exact mem_Icc.2 ⟨p.parts_pos hj', Nat.Partition.le_of_mem_parts hj'⟩
  rw [← Finset.prod_subset hsub (fun j _ hj => by
    have : p.parts.count j = 0 := Multiset.count_eq_zero.2 (by simpa using hj)
    simp [this])]
  have e1 : ∏ j ∈ p.parts.toFinset, (θ / j) ^ p.parts.count j / (p.parts.count j).factorial =
      θ ^ p.parts.card * partWeight F p.parts := by
    simp only [div_eq_mul_inv, mul_pow, inv_pow, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib]
    rw [Finset.prod_pow_eq_pow_sum, Multiset.toFinset_sum_count_eq]
    unfold partWeight
    rw [mul_inv, Finset.prod_multiset_count p.parts]
    push_cast
    ring
  rw [e1]
  unfold esf
  ring

theorem sum_esf [CharZero F] (θ : F) (n : ℕ) (h : (ascPochhammer F n).eval θ ≠ 0) :
    ∑ p : Nat.Partition n, esf θ p = 1 := by
  have hn : (n.factorial : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  unfold esf
  rw [← Finset.sum_div, div_eq_one_iff_eq h]
  have := sum_partWeight_mul_pow θ n
  calc ∑ p : Nat.Partition n, (n.factorial : F) * θ ^ p.parts.card * partWeight F p.parts
      = (n.factorial : F) * ∑ p : Nat.Partition n, partWeight F p.parts * θ ^ p.parts.card := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ = _ := by rw [this, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

theorem esf_nonneg [LinearOrder F] [IsStrictOrderedRing F] {θ : F} (hθ : 0 < θ) {n : ℕ}
    (p : Nat.Partition n) : 0 ≤ esf θ p := by
  have hP := (ascPochhammer_pos n θ hθ).le
  unfold esf
  refine div_nonneg ?_ hP
  unfold partWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hθ.le _))
    (inv_nonneg.2 (mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)))

theorem sum_esf_card [CharZero F] (θ : F) (n k : ℕ) :
    ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.parts.card = k),
      esf θ p = (Nat.stirlingFirst n k : F) * θ ^ k / (ascPochhammer F n).eval θ := by
  unfold esf
  rw [← Finset.sum_div]
  congr 1
  rw [← factorial_mul_sum_partWeight_card, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.1 hp).2]
  ring

theorem eval_derivative_ascPochhammer_succ (θ : F) (n : ℕ) :
    ((ascPochhammer F (n + 1)).derivative).eval θ =
      ((ascPochhammer F n).derivative).eval θ * (θ + n) + (ascPochhammer F n).eval θ := by
  rw [ascPochhammer_succ_right, derivative_mul]
  simp

theorem mul_eval_derivative_ascPochhammer (θ : F) (n : ℕ) (h : ∀ i < n, θ + i ≠ 0) :
    θ * ((ascPochhammer F n).derivative).eval θ =
      (∑ i ∈ range n, θ / (θ + i)) * (ascPochhammer F n).eval θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun i hi => h i (by omega)
    have hn := h n (by omega)
    rw [eval_derivative_ascPochhammer_succ, ascPochhammer_succ_eval, Finset.sum_range_succ]
    have : θ * ((ascPochhammer F n).derivative.eval θ * (θ + n)) =
        (θ * (ascPochhammer F n).derivative.eval θ) * (θ + n) := by ring
    rw [mul_add, this, ih']
    field_simp

theorem sum_card_mul_partWeight_pow [CharZero F] (θ : F) (n : ℕ) :
    ∑ p : Nat.Partition n, (p.parts.card : F) * (partWeight F p.parts * θ ^ p.parts.card) =
      θ * ((n.factorial : F)⁻¹ * ((ascPochhammer F n).derivative).eval θ) := by
  have h := congrArg (fun q : F[X] => θ * q.derivative.eval θ) (cycleIndex_eq (F := F) n)
  simp only [derivative_C_mul, eval_mul, eval_C] at h
  rw [← h, cycleIndex, derivative_sum, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases hc : p.parts.card with _ | c
  · simp
  · simp only [derivative_C_mul, derivative_X_pow, eval_mul, eval_C, eval_X, eval_pow,
      Nat.add_sub_cancel]
    push_cast
    ring

theorem sum_card_mul_esf [CharZero F] (θ : F) (n : ℕ) (h : ∀ i < n, θ + i ≠ 0) :
    ∑ p : Nat.Partition n, (p.parts.card : F) * esf θ p = ∑ i ∈ range n, θ / (θ + i) := by
  have hP : (ascPochhammer F n).eval θ ≠ 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ascPochhammer_succ_eval]
      exact mul_ne_zero (ih fun i hi => h i (by omega)) (h n (by omega))
  have hn : (n.factorial : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h1 := sum_card_mul_partWeight_pow θ n
  have h2 := mul_eval_derivative_ascPochhammer θ n h
  have e : ∀ p : Nat.Partition n, (p.parts.card : F) * esf θ p =
      (n.factorial : F) / (ascPochhammer F n).eval θ *
        ((p.parts.card : F) * (partWeight F p.parts * θ ^ p.parts.card)) := by
    intro p; unfold esf; ring
  rw [Finset.sum_congr rfl fun p _ => e p, ← Finset.mul_sum, h1]
  rw [div_mul_eq_mul_div, div_eq_iff hP]
  calc (n.factorial : F) * (θ * ((n.factorial : F)⁻¹ * ((ascPochhammer F n).derivative).eval θ))
      = θ * ((ascPochhammer F n).derivative).eval θ := by field_simp
    _ = _ := h2

end Rhone.Probability
