/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Push

/-! # The row slack `slack(i,j,t)` and its closed forms -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

def slack {R : Type*} [CommRing R] (i j t : R) : R :=
  (i + j - t) * (i + j - t - 1) - 2 * (i - t) * (j - t)

def bigS {R : Type*} [CommRing R] (i j : R) : R := i * (i - 1) + j * (j - 1)

section Ring

variable {R : Type*} [CommRing R] (i j t : R)

theorem slack_eq_exitCount :
    slack i j t = (i - t) * (i - t - 1) + (j - t) * (j - t - 1) + t * (t - 1)
      + 2 * t * (i + j - 2 * t) := by
  unfold slack; ring

theorem slack_eq_closed : slack i j t = bigS i j - t * (t - 1) := by
  unfold slack bigS; ring

theorem slack_zero : slack i j 0 = bigS i j := by
  rw [slack_eq_closed]; ring

theorem slack_one : slack i j 1 = bigS i j := by
  rw [slack_eq_closed]; ring

end Ring

theorem slack_intCast (i j t : ℤ) :
    ((slack i j t : ℤ) : ℝ) = slack (i : ℝ) (j : ℝ) (t : ℝ) := by
  unfold slack; push_cast; ring

theorem bigS_intCast (i j : ℤ) : ((bigS i j : ℤ) : ℝ) = bigS (i : ℝ) (j : ℝ) := by
  unfold bigS; push_cast; ring

theorem mul_pred_nonneg {b : ℤ} (hb : 0 ≤ b) : 0 ≤ b * (b - 1) := by
  rcases lt_or_ge b 1 with h | h
  · have hb0 : b = 0 := by omega
    simp [hb0]
  · exact mul_nonneg hb (by omega)

theorem mul_pred_mono {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) : a * (a - 1) ≤ b * (b - 1) := by
  rcases lt_or_ge a 1 with h | h
  · have ha0 : a = 0 := by omega
    subst ha0
    simpa using mul_pred_nonneg (ha.trans hab)
  · nlinarith [mul_nonneg (sub_nonneg.2 hab) (show (0:ℤ) ≤ b + a - 1 by omega)]

variable {i j t : ℤ}

theorem slack_nonneg (ht : 0 ≤ t) (hti : t ≤ i) (htj : t ≤ j) : 0 ≤ slack i j t := by
  rw [slack_eq_closed]
  have h1 : t * (t - 1) ≤ i * (i - 1) := mul_pred_mono ht hti
  have h2 : (0:ℤ) ≤ j * (j - 1) := mul_pred_nonneg (ht.trans htj)
  unfold bigS
  linarith

theorem slack_eq_zero_iff (ht : 0 ≤ t) (hti : t ≤ i) (htj : t ≤ j) :
    slack i j t = 0 ↔ (t = 0 ∧ i ≤ 1 ∧ j ≤ 1) ∨ (t = 1 ∧ i = 1 ∧ j = 1) := by
  rw [slack_eq_closed]
  constructor
  · intro h
    have h1 : t * (t - 1) ≤ i * (i - 1) := mul_pred_mono ht hti
    have h2 : (0:ℤ) ≤ j * (j - 1) := mul_pred_nonneg (ht.trans htj)
    unfold bigS at h
    have hj : j * (j - 1) = 0 := by linarith
    have hj1 : j = 0 ∨ j = 1 := by
      rcases mul_eq_zero.1 hj with h' | h' <;> omega
    have ht01 : t = 0 ∨ t = 1 := by omega
    have htt : t * (t - 1) = 0 := by rcases ht01 with h' | h' <;> simp [h']
    have hi : i * (i - 1) = 0 := by linarith
    have hi1 : i = 0 ∨ i = 1 := by
      rcases mul_eq_zero.1 hi with h' | h' <;> omega
    rcases ht01 with h' | h'
    · exact Or.inl ⟨h', by omega, by omega⟩
    · exact Or.inr ⟨h', by omega, by omega⟩
  · rintro (⟨rfl, hi, hj⟩ | ⟨rfl, rfl, rfl⟩)
    · unfold bigS
      have hi0 : i = 0 ∨ i = 1 := by omega
      have hj0 : j = 0 ∨ j = 1 := by omega
      rcases hi0 with h | h <;> rcases hj0 with h' | h' <;> simp [h, h']
    · unfold bigS; ring

theorem slack_le_bigS (ht : 0 ≤ t) : slack i j t ≤ bigS i j := by
  rw [slack_eq_closed]
  have := mul_pred_nonneg ht
  linarith

theorem slack_min_le {m : ℤ} (ht : 0 ≤ t) (htm : t ≤ m) :
    slack i j m ≤ slack i j t := by
  rw [slack_eq_closed, slack_eq_closed]
  have := mul_pred_mono ht htm
  linarith

theorem slack_min_eq {m : ℤ} : slack i j m = bigS i j - m * (m - 1) :=
  slack_eq_closed i j m

end Rhone.LinearAlgebra.Spectral
