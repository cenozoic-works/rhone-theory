/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic
/-! # Rational series approximations of the logarithm with explicit error bounds -/

@[expose] public section
namespace Rhone.Computation.RationalLogBounds

def argument (x : Rat) : Rat := (x - 1) / (x + 1)
def series (x : Rat) (n : Nat) : Rat :=
  2 * ∑ i ∈ Finset.range n, argument x ^ (2 * i + 1) / (2 * i + 1 : Rat)
def errorBound (x : Rat) (n : Nat) : Rat :=
  2 * |argument x| ^ (2 * n + 1) / (1 - argument x ^ 2)

lemma argument_abs_lt_one {x : Rat} (hx : 0 < x) : |argument x| < 1 := by
  have hden : 0 < x + 1 := by linarith
  rw [abs_lt]
  unfold argument
  constructor
  · apply (lt_div_iff₀ hden).mpr
    linarith
  · apply (div_lt_iff₀ hden).mpr
    linarith

lemma argument_ratio {x : Rat} (hx : 0 < x) :
    (1 + argument x) / (1 - argument x) = x := by
  have hden : x + 1 ≠ 0 := by linarith
  have harg : 1 - argument x ≠ 0 := by
    have h := (abs_lt.mp (argument_abs_lt_one hx)).2
    linarith
  unfold argument at *
  field_simp
  ring

lemma series_cast (x : Rat) (n : Nat) :
    (series x n : Real) =
      2 * ∑ i ∈ Finset.range n,
        (argument x : Real) ^ (2 * i + 1) / (2 * i + 1 : Real) := by
  simp [series]

lemma log_error {x : Rat} (hx : 0 < x) (n : Nat) :
    |Real.log (x : Real) - (series x n : Real)| ≤ (errorBound x n : Real) := by
  have harg : |(argument x : Real)| < 1 := by exact_mod_cast argument_abs_lt_one hx
  have hr : (1 + (argument x : Real)) / (1 - (argument x : Real)) = (x : Real) := by
    exact_mod_cast argument_ratio hx
  have h := Real.sum_range_sub_log_div_le harg n
  rw [hr] at h
  rw [series_cast]
  have heq : Real.log (x : Real) -
      2 * ∑ i ∈ Finset.range n,
        (argument x : Real) ^ (2 * i + 1) / (2 * i + 1 : Real) =
      2 * (1 / 2 * Real.log (x : Real) -
        ∑ i ∈ Finset.range n,
          (argument x : Real) ^ (2 * i + 1) / (2 * i + 1 : Real)) := by ring
  rw [heq, abs_mul]
  have hm := mul_le_mul_of_nonneg_left h (show (0 : Real) ≤ 2 by norm_num)
  simpa [errorBound, mul_div_assoc] using hm

def accepted (x claimed budget : Rat) (n : Nat) : Bool :=
  decide (0 < x ∧ |claimed - series x n| + errorBound x n ≤ budget)

lemma accepted_sound {x claimed budget : Rat} {n : Nat}
    (h : accepted x claimed budget n = true) :
    |(claimed : Real) - Real.log (x : Real)| ≤ (budget : Real) := by
  simp only [accepted, decide_eq_true_eq] at h
  have hb : |(claimed : Real) - (series x n : Real)| + (errorBound x n : Real) ≤ budget := by
    exact_mod_cast h.2
  have he := log_error h.1 n
  calc
    |(claimed : Real) - Real.log (x : Real)| =
        |((claimed : Real) - (series x n : Real)) +
          ((series x n : Real) - Real.log (x : Real))| := by congr 1; ring
    _ ≤ |(claimed : Real) - (series x n : Real)| +
        |(series x n : Real) - Real.log (x : Real)| := abs_add_le _ _
    _ ≤ |(claimed : Real) - (series x n : Real)| + (errorBound x n : Real) := by
      rw [abs_sub_comm] at he
      exact add_le_add le_rfl he
    _ ≤ budget := hb

def normalizedSeries (u : Rat) (e : Int) (n : Nat) : Rat :=
  series u n + (e : Rat) * series 2 n

def normalizedError (u : Rat) (e : Int) (n : Nat) : Rat :=
  errorBound u n + |(e : Rat)| * errorBound 2 n

lemma normalized_log_error {u : Rat} (hu : 0 < u) (e : Int) (n : Nat) :
    |Real.log ((u * (2 : Rat) ^ e : Rat) : Real) -
      (normalizedSeries u e n : Real)| ≤ (normalizedError u e n : Real) := by
  have h := log_error hu n
  have h2 := log_error (show (0 : Rat) < 2 by norm_num) n
  have hu' : (u : Real) ≠ 0 := ne_of_gt (by exact_mod_cast hu)
  have hpow : ((2 : Real) ^ e) ≠ 0 := zpow_ne_zero e (by norm_num)
  push_cast
  rw [Real.log_mul hu' hpow, Real.log_zpow]
  have heq : Real.log (u : Real) + (e : Real) * Real.log 2 -
      (normalizedSeries u e n : Real) =
      (Real.log (u : Real) - (series u n : Real)) +
        (e : Real) * (Real.log 2 - (series 2 n : Real)) := by
    simp [normalizedSeries]
    ring
  rw [heq]
  calc
    |(Real.log (u : Real) - (series u n : Real)) +
        (e : Real) * (Real.log 2 - (series 2 n : Real))| ≤
        |Real.log (u : Real) - (series u n : Real)| +
          |(e : Real) * (Real.log 2 - (series 2 n : Real))| := abs_add_le _ _
    _ ≤ (errorBound u n : Real) + |(e : Real)| * (errorBound 2 n : Real) := by
      rw [abs_mul]
      exact add_le_add h (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = (normalizedError u e n : Real) := by simp [normalizedError]

def checkNormalized (x claimed budget : Rat) (e : Int) (n : Nat) : Bool :=
  let u := x / (2 : Rat) ^ e
  decide (0 < x ∧ |claimed - normalizedSeries u e n| + normalizedError u e n ≤ budget)

lemma checkNormalized_sound {x claimed budget : Rat} {e : Int} {n : Nat}
    (h : checkNormalized x claimed budget e n = true) :
    |(claimed : Real) - Real.log (x : Real)| ≤ (budget : Real) := by
  dsimp only [checkNormalized] at h
  simp only [decide_eq_true_eq] at h
  have hp : (0 : Rat) < 2 ^ e := zpow_pos (by norm_num) e
  have hu : 0 < x / (2 : Rat) ^ e := div_pos h.1 hp
  have he := normalized_log_error hu e n
  rw [div_mul_cancel₀ x (ne_of_gt hp)] at he
  have hb : |(claimed : Real) - (normalizedSeries (x / 2 ^ e) e n : Real)| +
      (normalizedError (x / 2 ^ e) e n : Real) ≤ budget := by exact_mod_cast h.2
  calc
    |(claimed : Real) - Real.log (x : Real)| =
        |((claimed : Real) - (normalizedSeries (x / 2 ^ e) e n : Real)) +
          ((normalizedSeries (x / 2 ^ e) e n : Real) - Real.log (x : Real))| := by
      congr 1
      ring
    _ ≤ |(claimed : Real) - (normalizedSeries (x / 2 ^ e) e n : Real)| +
        |(normalizedSeries (x / 2 ^ e) e n : Real) - Real.log (x : Real)| := abs_add_le _ _
    _ ≤ |(claimed : Real) - (normalizedSeries (x / 2 ^ e) e n : Real)| +
        (normalizedError (x / 2 ^ e) e n : Real) := by
      rw [abs_sub_comm] at he
      exact add_le_add le_rfl he
    _ ≤ budget := hb

end Rhone.Computation.RationalLogBounds
