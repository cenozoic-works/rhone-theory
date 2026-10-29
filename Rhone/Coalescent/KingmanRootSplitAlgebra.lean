/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
/-! # Binomial harmonic algebra used in the two-colour history induction -/
@[expose] public section
namespace Rhone.Coalescent
noncomputable def rootSplitValue (a b : ℕ) : ℝ :=
  2 / (((a + b - 1 : ℕ) : ℝ) * ((a + b).choose a : ℝ))
theorem rootSplitValue_harmonic (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hk : 3 ≤ a + b) :
    (((a + b).choose 2 : ℕ) : ℝ) * rootSplitValue a b =
      (a.choose 2 : ℝ) * rootSplitValue (a - 1) b +
        (b.choose 2 : ℝ) * rootSplitValue a (b - 1) := by
  have hleft := Nat.add_one_mul_choose_eq (a + b - 1) (a - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a + b), Nat.sub_add_cancel ha] at hleft
  have hright := Nat.choose_mul_succ_eq (a + b - 1) a
  rw [Nat.sub_add_cancel (by omega : 1 ≤ a + b), show a + b - a = b by omega] at hright
  have hn0 : ((a + b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show a + b ≠ 0 by omega)
  have hc0 : ((a + b).choose a : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hm1 : ((a + b - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show a + b - 1 ≠ 0 by omega)
  have hm2 : ((a + b - 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show a + b - 2 ≠ 0 by omega)
  have hl : ((a + b - 1).choose (a - 1) : ℝ) =
      ((a + b).choose a : ℝ) * a / (a + b : ℕ) := by
    apply (eq_div_iff hn0).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using hleft)
  have hr : ((a + b - 1).choose a : ℝ) =
      ((a + b).choose a : ℝ) * b / (a + b : ℕ) := by
    apply (eq_div_iff hn0).mpr
    exact_mod_cast hright
  unfold rootSplitValue
  rw [show a - 1 + b = a + b - 1 by omega,
    show a + (b - 1) = a + b - 1 by omega,
    show a + b - 1 - 1 = a + b - 2 by omega, hl, hr]
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
  rw [Nat.cast_sub (by omega : 1 ≤ a + b), Nat.cast_sub (by omega : 2 ≤ a + b)]
  rw [Nat.cast_sub (by omega : 1 ≤ a + b), Nat.cast_one] at hm1
  rw [Nat.cast_sub (by omega : 2 ≤ a + b), Nat.cast_ofNat] at hm2
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
  field_simp
  ring
end Rhone.Coalescent
