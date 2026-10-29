/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGFlatLaw
public import Mathlib.Order.Fin.Basic

/-! # Event times and strictly increasing clocks of valid flat ARG coordinates -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

theorem argFlatRun_event_time {n : ℕ} (z : AugmentedState) (w : Fin n → Action)
    (τ : Fin n → ℝ) (x : ℝ) (j : Fin n) :
    (argFlatRun z w τ x (j.val + 1)).1.1 = τ j := by
  rw [argFlatRun, dite_eq_left j.isLt]
  cases w j <;> rfl

theorem argFlatValid_measurable (N : ℕ) :
    MeasurableSet {p : ARGFlatCoordinate N | argFlatValid N p} := by
  have he : {p : ARGFlatCoordinate N | 0 < argFlatDensity N 2 p} =
      {p | argFlatValid N p} := by
    ext p
    by_cases hp : argFlatValid N p
    · simp only [Set.mem_ofPred_eq, hp, iff_true]
      unfold argFlatDensity
      rw [ite_eq_left hp]
      positivity
    · simp only [Set.mem_ofPred_eq, hp, iff_false]
      unfold argFlatDensity
      rw [ite_eq_right hp]
      exact not_lt_of_ge le_rfl
  rw [← he]
  exact measurableSet_lt measurable_const (argFlatDensity_measurable N 2 (by norm_num))

theorem argFlatValid_clocks_strictMono (N : ℕ) (p : ARGFlatCoordinate N)
    (hp : argFlatValid N p) : StrictMono p.2.1 := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro j
  have hj := (hp.2.2.1 j.succ).2.2
  change (argFlatRun (initialState N, (0, .inl ())) p.1 p.2.1 p.2.2
    (j.val + 1)).1.1 < p.2.1 j.succ at hj
  have he := argFlatRun_event_time (initialState N, (0, .inl ())) p.1 p.2.1 p.2.2 j.castSucc
  simp only [Fin.val_castSucc] at he
  rw [he] at hj
  exact hj
end Rhone.Coalescent.SmcPrime
