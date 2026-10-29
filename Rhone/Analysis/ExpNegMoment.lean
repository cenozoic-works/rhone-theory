/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # The map `t ↦ exp(-t)` on `[0, ∞]` -/

@[expose] public section

namespace Rhone.Analysis.ExpNegMoment

open scoped ENNReal

noncomputable def expNeg (t : ℝ≥0∞) : ℝ≥0∞ := EReal.exp (-(t : EReal))

theorem continuous_expNeg : Continuous expNeg :=
  ENNReal.continuous_exp.comp (continuous_neg.comp continuous_coe_ennreal_ereal)

theorem measurable_expNeg : Measurable expNeg := continuous_expNeg.measurable

theorem expNeg_injective : Function.Injective expNeg := by
  intro s t h
  have h1 := EReal.exp_strictMono.injective h
  exact EReal.coe_ennreal_injective (neg_injective h1)

theorem expNeg_ofReal {s : ℝ} (hs : 0 ≤ s) :
    expNeg (ENNReal.ofReal s) = ENNReal.ofReal (Real.exp (-s)) := by
  rw [expNeg, EReal.coe_ennreal_ofReal, max_eq_left hs, ← EReal.coe_neg, EReal.exp_coe]

theorem expNeg_zero : expNeg 0 = 1 := by
  simp [expNeg]

theorem expNeg_top : expNeg ⊤ = 0 := by
  simp [expNeg]

theorem expNeg_le_one (t : ℝ≥0∞) : expNeg t ≤ 1 := by
  rw [expNeg, EReal.exp_le_one_iff, EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg t

theorem expNeg_ne_top (t : ℝ≥0∞) : expNeg t ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (expNeg_le_one t)

theorem expNeg_add (s t : ℝ≥0∞) : expNeg (s + t) = expNeg s * expNeg t := by
  rw [expNeg, expNeg, expNeg, EReal.coe_ennreal_add, EReal.neg_add
    (Or.inl (EReal.coe_ennreal_ne_bot s)) (Or.inr (EReal.coe_ennreal_ne_bot t)),
    sub_eq_add_neg, EReal.exp_add]

end Rhone.Analysis.ExpNegMoment
