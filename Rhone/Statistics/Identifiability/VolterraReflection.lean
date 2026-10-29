/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PeanoBaker
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Time reflection of locally integrable Volterra series terms -/

@[expose] public section

open Set Filter MeasureTheory

namespace Rhone.Statistics.Identifiability.PeanoBaker

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem locallyIntegrable_reflection (A : ℝ → E →L[ℝ] E)
    (hA : LocallyIntegrable A volume) :
    LocallyIntegrable (fun t => -A (-t)) volume := by
  have h : LocallyIntegrable (fun t => A (-t)) volume := by
    have hmap := (locallyIntegrable_map_homeomorph (Homeomorph.neg ℝ)
      (f := A) (μ := volume))
    apply hmap.mp
    change LocallyIntegrable A (Measure.map Neg.neg volume)
    rw [Measure.map_neg_eq_self]
    exact hA
  exact h.neg

theorem term_reflection (A : ℝ → E →L[ℝ] E) (x : E) (n : ℕ) (t : ℝ) :
    term (fun s => -A (-s)) x n t = term A x n (-t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [term_succ, ih, neg_apply]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (fun s => A s (term A x
      n s)),
      neg_zero, intervalIntegral.integral_symm]
    simp

end Rhone.Statistics.Identifiability.PeanoBaker
