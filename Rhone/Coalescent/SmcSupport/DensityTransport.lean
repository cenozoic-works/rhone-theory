/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.ARGTransitionDensity

/-! # Transport of chronological densities through measurable coordinate changes -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open MeasureTheory
open scoped ENNReal

theorem map_withDensity_equiv {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (e : Ω ≃ᵐ Ξ) (μ : Measure Ω) (w : Ω → ℝ≥0∞)
    (hw : Measurable w) :
    (μ.withDensity w).map e =
      (μ.map e).withDensity (fun y => w (e.symm y)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, e.restrict_map,
    lintegral_map (show Measurable (fun y => w (e.symm y)) from
      hw.comp e.symm.measurable) e.measurable]
  simp only [e.symm_apply_apply]

end Rhone.Coalescent.SmcSupport
