/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.LDDecay
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic

/-!
# Finite-array linkage disequilibrium and neutral deterministic recombination

Source: burger2000, ch. 2. -/

@[expose] public section
namespace Rhone.Dynamics.MultialleleLD
open Finset
variable {A B : Type*} [Fintype A] [Fintype B]

def row (x : A → B → ℝ) (a : A) : ℝ := ∑ b, x a b
def col (x : A → B → ℝ) (b : B) : ℝ := ∑ a, x a b
def ld (x : A → B → ℝ) (a : A) (b : B) : ℝ := x a b - row x a * col x b
def recombine (c : ℝ) (x : A → B → ℝ) (a : A) (b : B) : ℝ :=
  (1-c)*x a b + c*row x a*col x b

/-- Source: burger2000, ch. 2. -/
theorem row_recombine (c : ℝ) (x : A → B → ℝ)
    (ht : ∑ a, ∑ b, x a b = 1) (a : A) : row (recombine c x) a = row x a := by
  have hc : ∑ b, col x b = 1 := by
    unfold col
    rw [sum_comm]
    exact ht
  simp only [row, recombine, sum_add_distrib, ← mul_sum, hc, mul_one]
  ring

/-- Source: burger2000, ch. 2. -/
theorem col_recombine (c : ℝ) (x : A → B → ℝ)
    (ht : ∑ a, ∑ b, x a b = 1) (b : B) : col (recombine c x) b = col x b := by
  have hr : ∑ a, row x a = 1 := ht
  unfold col recombine
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul, hr, mul_one, col]
  ring

/-- Source: burger2000, ch. 2. -/
theorem ld_recombine (c : ℝ) (x : A → B → ℝ)
    (ht : ∑ a, ∑ b, x a b = 1) (a : A) (b : B) :
    ld (recombine c x) a b = (1-c)*ld x a b := by
  rw [ld, row_recombine c x ht, col_recombine c x ht]
  simp only [recombine, ld]
  ring

/-- Source: burger2000, ch. 2. -/
theorem recombine_total (c : ℝ) (x : A → B → ℝ)
    (ht : ∑ a, ∑ b, x a b = 1) : ∑ a, ∑ b, recombine c x a b = 1 := by
  change ∑ a, row (recombine c x) a = 1
  simp_rw [row_recombine c x ht]
  exact ht

/-- Source: burger2000, ch. 2. -/
theorem ld_iterate (c : ℝ) (x : A → B → ℝ)
    (ht : ∑ a, ∑ b, x a b = 1) (t : ℕ) (a : A) (b : B) :
    ld ((recombine c)^[t] x) a b = (1-c)^t*ld x a b := by
  have htotal : ∀ s, ∑ a, ∑ b, ((recombine c)^[s] x) a b = 1 := by
    intro s
    induction s with
    | zero => simpa using ht
    | succ s ih =>
      rw [Function.iterate_succ_apply']
      exact recombine_total c _ ih
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ld_recombine c _ (htotal t), ih, pow_succ]
    ring

/-- Source: burger2000, ch. 2. -/
theorem row_ld_sum_zero (x : A → B → ℝ)
    (ht : ∑ a, ∑ b, x a b = 1) (a : A) : ∑ b, ld x a b = 0 := by
  have hc : ∑ b, col x b = 1 := by
    unfold col
    rw [sum_comm]
    exact ht
  simp [ld, sum_sub_distrib, ← mul_sum, hc, row]

/-- Source: burger2000, ch. 2. -/
theorem col_ld_sum_zero (x : A → B → ℝ)
    (ht : ∑ a, ∑ b, x a b = 1) (b : B) : ∑ a, ld x a b = 0 := by
  have hr : ∑ a, row x a = 1 := ht
  simp [ld, sum_sub_distrib, ← sum_mul, hr, col]

/-- Source: burger2000, ch. 2. -/
theorem ld_eq_zero_iff_product (x : A → B → ℝ) :
    (∀ a b, ld x a b = 0) ↔ ∀ a b, x a b = row x a*col x b := by
  simp only [ld, sub_eq_zero]

/-- Source: burger2000, ch. 2. -/
theorem recombine_preserves_distribution (c : ℝ) (x : A → B → ℝ)
    (hx : ∀ a b, 0 ≤ x a b) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ht : ∑ a, ∑ b, x a b = 1) :
    (∀ a b, 0 ≤ recombine c x a b) ∧ (∑ a, ∑ b, recombine c x a b = 1) := by
  constructor
  · intro a b
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hc1) (hx a b))
      (mul_nonneg (mul_nonneg hc0 (sum_nonneg fun j _ => hx a j))
        (sum_nonneg fun i _ => hx i b))
  · exact recombine_total c x ht

end Rhone.Dynamics.MultialleleLD
