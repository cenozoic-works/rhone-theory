/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanThreeRectangleCDF
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # A parameter-free probability-rectangle statistic for the three-sample pan family -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace ThreeSampleCDF

def firstSurvival (μ : Measure (ℝ × ℝ)) (t : ℝ) : ℝ :=
  1 - (μ.map Prod.fst).real (Ioc 0 t)

def clockRoot (μ : Measure (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (firstSurvival μ t) ^ (1 / 3 : ℝ)

def rectangleResidual (μ : Measure (ℝ × ℝ)) (s t : ℝ) : ℝ :=
  μ.real (Ioc 0 s ×ˢ Ioi t) - (3 / 2 : ℝ) * clockRoot μ t * (1 - (clockRoot μ s)^2)

lemma pan_clockRoot (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop)
    {t : ℝ} (ht : 0 ≤ t) :
    clockRoot (PanThreeSample.law rate) t = Real.exp (-integratedClock rate t) := by
  unfold clockRoot firstSurvival
  rw [PanThreeSample.first_survival rate hr hn htail ht,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

theorem pan_rectangleResidual_zero (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    rectangleResidual (PanThreeSample.law rate) s t = 0 := by
  unfold rectangleResidual
  rw [pan_clockRoot rate hr hn htail hs, pan_clockRoot rate hr hn htail (hs.trans hst),
    PanThreeSample.law_real_prefix_tail_clock rate hr hn htail hs hst, sub_self]

theorem pan_rectangleResidual_zero_halfLine (rate : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    rectangleResidual (PanThreeSample.law rate) s t = 0 := by
  rw [PanThreeSample.law_congr_halfLine_ae (PanThreeSample.representative_eq_ae hn)]
  exact pan_rectangleResidual_zero _ (PanThreeSample.representative_locallyIntegrable hr)
    (PanThreeSample.representative_nonneg rate)
    (PanThreeSample.representative_clock_diverges hn htail) hs hst

end ThreeSampleCDF
end Rhone.Statistics.Identifiability
