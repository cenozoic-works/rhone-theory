/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PositivePrefixMeasure

/-! # Proper positive-time observations have vanishing survival tails -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability

lemma positive_probability_survival_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hp : ∀ᵐ t ∂μ, 0 < t) :
    Tendsto (fun t => 1 - μ.real (Ioc 0 t)) atTop (𝓝 0) := by
  have he := tendsto_measure_Iic_atTop μ
  rw [measure_univ] at he
  have hr : Tendsto (fun t => μ.real (Iic t)) atTop (𝓝 1) := by
    simpa only [Measure.real, ENNReal.toReal_one, Function.comp_def] using
      (ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).tendsto.comp he
  have h := hr.const_sub 1
  simpa only [sub_self, real_Iic_eq_Ioc_of_positive μ hp] using h

end Rhone.Statistics.Identifiability
