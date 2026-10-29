/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.CompactMoments

/-! # Identification of every proper pan observer with the compact candidate family -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator FiniteBlockModel
open Algebra.Identifiability MarkovChain.Identifiability Identifiability

def clampTime (x : ℝ) : CompactTime :=
  ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clamp_time_continuous : Continuous clampTime := by
  unfold clampTime
  fun_prop

def compactify (μ : Measure ℝ) [IsProbabilityMeasure μ] : ProbabilityMeasure CompactTime :=
  ⟨μ.map clampTime, inferInstance⟩

theorem realized_compactify (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1) : realized (compactify μ) = μ := by
  change Measure.map Subtype.val (μ.map clampTime) = μ
  rw [Measure.map_map measurable_subtype_coe clamp_time_continuous.measurable]
  calc
    μ.map (Subtype.val ∘ clampTime) = μ.map id := by
      apply Measure.map_congr
      filter_upwards [hμ] with x hx
      simp [clampTime, min_eq_right hx.2, max_eq_right hx.1]
    _ = μ := Measure.map_id

theorem pan_compact (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {k : ℝ} (hk : 0 ≤ k) :
    let := PanThreeSample.durationLaw_probability r hr hn ht
    let := panClockLaw_probability k r hr hn ht
    encodedProbability k (uniformLift (PanThreeSample.durationLaw r)) =
      compactPan (compactify (panClockLaw k r)) := by
  let := PanThreeSample.durationLaw_probability r hr hn ht
  let := panClockLaw_probability k r hr hn ht
  dsimp only
  apply ProbabilityMeasure.toMeasure_injective
  apply compact_moment_unique 3
  intro n
  change monoMoment n (encodedProbability k (uniformLift (PanThreeSample.durationLaw r))) =
    monoMoment n (compactPan (compactify (panClockLaw k r)))
  rw [uniform_lift_monomial hk _ (PanThreeSample.durationLaw_nonnegative r),
    compact_pan_monomial]
  apply Finset.sum_congr rfl
  intro q _
  rw [pan_duration_sorted_moment r hr hn ht hk]
  unfold pairMoment
  rw [realized_compactify _ (panClockLaw_unit_support k r)]

end Rhone.Statistics.WeakRegularSeparation
