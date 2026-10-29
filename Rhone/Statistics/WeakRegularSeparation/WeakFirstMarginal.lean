/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ProfileFirstMarginal

/-! # First-marginal reconstruction allowing a zero internal branch -/

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Rhone.Statistics.WeakRegularSeparation
open MarkovChain.Identifiability Identifiability Identifiability.ThreeSampleMembership

theorem weak_first_marginal_eq (P : FirstSurvivalProfile) (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] (hu : ∀ᵐ p ∂μ, 0 < p.1)
    (hm : P.Matches μ) : μ.map Prod.fst = (PanThreeSample.law P.rate).map Prod.fst := by
  let := PanThreeSample.isProbability P.rate P.rate_locallyIntegrable
    P.rate_nonnegative P.clock_diverges
  let : IsProbabilityMeasure (μ.map Prod.fst) :=
    inferInstance
  let : IsProbabilityMeasure ((PanThreeSample.law P.rate).map Prod.fst) :=
    inferInstance
  have hμ : ∀ᵐ t ∂μ.map Prod.fst, 0 < t :=
    (ae_map_iff measurable_fst.aemeasurable measurableSet_Ioi).mpr hu
  have hν : ∀ᵐ t ∂(PanThreeSample.law P.rate).map Prod.fst, 0 < t := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Ioi).mpr
    filter_upwards [PanThreeSample.law_ordered_support P.rate] with t ht
    exact ht.1
  apply positive_measure_eq_of_prefix _ _ hμ hν
  intro t ht
  have h1 := hm t ht
  have h2 := P.pan_matches t ht
  unfold ThreeSampleCDF.firstSurvival at h1 h2
  linarith

theorem candidate_duration_first_marginal (P : FirstSurvivalProfile) :
    (PanThreeSample.durationLaw P.rate).map Prod.fst =
      (PanThreeSample.law P.rate).map Prod.fst := by
  unfold PanThreeSample.durationLaw
  rw [Measure.map_map measurable_fst PanThreeSample.measurable_toDurations]
  rfl

end Rhone.Statistics.WeakRegularSeparation
