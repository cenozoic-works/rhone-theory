/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.RationalLogBounds
public import Rhone.Computation.RatRounding
/-! # Certified nearest grid value of the logarithm of a rational -/

@[expose] public section
namespace Rhone.Computation.NearestLog

def accepted (x step : Rat) (k e : Int) (n : Nat) : Bool :=
  let u := x / (2 : Rat) ^ e
  let mid := RationalLogBounds.normalizedSeries u e n
  let err := RationalLogBounds.normalizedError u e n
  decide (0 < x ∧ 0 < step ∧
    step * ((k : Rat) - 1 / 2) < mid - err ∧
    mid + err < step * ((k : Rat) + 1 / 2))

lemma accepted_error {x step : Rat} {k e : Int} {n : Nat}
    (h : accepted x step k e n = true) :
    |(step : Real) * (k : Real) - Real.log (x : Real)| < (step : Real) / 2 := by
  dsimp only [accepted] at h
  simp only [decide_eq_true_eq] at h
  have hp : (0 : Rat) < 2 ^ e := zpow_pos (by norm_num) e
  have he := RationalLogBounds.normalized_log_error (div_pos h.1 hp) e n
  rw [div_mul_cancel₀ x (ne_of_gt hp)] at he
  have hlo : (step : Real) * ((k : Real) - 1 / 2) <
      (RationalLogBounds.normalizedSeries (x / 2 ^ e) e n : Real) -
        (RationalLogBounds.normalizedError (x / 2 ^ e) e n : Real) := by
    have hc : ((step * ((k : Rat) - 1 / 2) : Rat) : Real) <
        ((RationalLogBounds.normalizedSeries (x / 2 ^ e) e n -
          RationalLogBounds.normalizedError (x / 2 ^ e) e n : Rat) : Real) := by
      exact_mod_cast h.2.2.1
    push_cast at hc
    exact hc
  have hhi : (RationalLogBounds.normalizedSeries (x / 2 ^ e) e n : Real) +
      (RationalLogBounds.normalizedError (x / 2 ^ e) e n : Real) <
        (step : Real) * ((k : Real) + 1 / 2) := by
    have hc : ((RationalLogBounds.normalizedSeries (x / 2 ^ e) e n +
        RationalLogBounds.normalizedError (x / 2 ^ e) e n : Rat) : Real) <
        ((step * ((k : Rat) + 1 / 2) : Rat) : Real) := by
      exact_mod_cast h.2.2.2
    push_cast at hc
    exact hc
  obtain ⟨hl, hh⟩ := abs_le.mp he
  rw [abs_lt]
  constructor <;> linarith

lemma accepted_unique_nearest {x step : Rat} {k e : Int} {n : Nat}
    (h : accepted x step k e n = true) (j : Int) (hj : j ≠ k) :
    |(step : Real) * (k : Real) - Real.log (x : Real)| <
      |(step : Real) * (j : Real) - Real.log (x : Real)| := by
  have he := accepted_error h
  have hs : (0 : Real) < step := by
    dsimp only [accepted] at h
    simp only [decide_eq_true_eq] at h
    exact_mod_cast h.2.1
  have hdistInt : (1 : Int) ≤ |j - k| := by
    have hne : j - k ≠ 0 := sub_ne_zero.mpr hj
    have hp : (0 : Int) < |j - k| := abs_pos.mpr hne
    omega
  have hdist : (1 : Real) ≤ |(j : Real) - (k : Real)| := by
    exact_mod_cast hdistInt
  have hsep : (step : Real) ≤ |(step : Real) * j - (step : Real) * k| := by
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    simpa using mul_le_mul_of_nonneg_left hdist hs.le
  have ht := abs_sub_le ((step : Real) * j) (Real.log (x : Real)) ((step : Real) * k)
  rw [abs_sub_comm (Real.log (x : Real)) ((step : Real) * k)] at ht
  linarith

end Rhone.Computation.NearestLog

namespace Rhone.Computation.NearestLog

def candidateIndex (x step : Rat) (e : Int) (n : Nat) : Int :=
  RatRounding.nearestEven (RationalLogBounds.normalizedSeries (x / (2 : Rat) ^ e) e n / step)

def checked (x step : Rat) (e : Int) (n : Nat) : Option Int :=
  let k := candidateIndex x step e n
  if accepted x step k e n then some k else none

lemma checked_some {x step : Rat} {e k : Int} {n : Nat}
    (h : checked x step e n = some k) : accepted x step k e n = true := by
  dsimp only [checked] at h
  split_ifs at h with hc
  · exact (Option.some.inj h) ▸ hc

lemma checked_error {x step : Rat} {e k : Int} {n : Nat}
    (h : checked x step e n = some k) :
    |(step : Real) * (k : Real) - Real.log (x : Real)| < (step : Real) / 2 :=
  accepted_error (checked_some h)

lemma checked_nearest {x step : Rat} {e k : Int} {n : Nat}
    (h : checked x step e n = some k) (j : Int) (hj : j ≠ k) :
    |(step : Real) * (k : Real) - Real.log (x : Real)| <
      |(step : Real) * (j : Real) - Real.log (x : Real)| :=
  accepted_unique_nearest (checked_some h) j hj

lemma checked_refuses {x step : Rat} {e : Int} {n : Nat}
    (h : accepted x step (candidateIndex x step e n) e n = false) :
    checked x step e n = none := by simp [checked, h]

end Rhone.Computation.NearestLog
