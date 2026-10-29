/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependenceBudget.Transfer
public import Mathlib.MeasureTheory.Measure.Real

/-! # Exact finite probability weights for existing observation measures -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteRobustness
open DependenceBudget
variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

noncomputable def finiteLaw (μ : Measure X) [IsProbabilityMeasure μ] : Law X where
  mass := fun x => μ.real {x}
  nonneg := fun _ => measureReal_nonneg
  total := by simp

noncomputable def finiteTV (μ ν : Measure X) : ℝ :=
  (∑ x, |μ.real {x} - ν.real {x}|) / 2

theorem finite_law_tv (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariation (finiteLaw μ) (finiteLaw ν) = finiteTV μ ν := rfl

end Rhone.Statistics.ThreeSiteRobustness
