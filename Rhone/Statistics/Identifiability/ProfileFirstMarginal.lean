/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RegularFirstSurvivalProfile
public import Rhone.Statistics.Identifiability.PositivePrefixMeasure

/-! # First marginal of a law matching a first-survival profile equals the pan first marginal -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership
open ThreeSampleCDF

namespace FirstSurvivalProfile

def Matches (P : FirstSurvivalProfile) (μ : Measure (ℝ × ℝ)) : Prop :=
  ∀ t, 0 ≤ t → firstSurvival μ t = P.survival t

lemma pan_matches (P : FirstSurvivalProfile) : P.Matches (PanThreeSample.law P.rate) := by
  intro t ht
  exact (PanThreeSample.first_survival P.rate P.rate_locallyIntegrable
    P.rate_nonnegative P.clock_diverges ht).trans (P.survival_eq_clock ht).symm

lemma first_marginal_eq (P : FirstSurvivalProfile) (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] (ho : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 < p.2) (hm : P.Matches μ) :
    μ.map Prod.fst = (PanThreeSample.law P.rate).map Prod.fst := by
  let : IsProbabilityMeasure (PanThreeSample.law P.rate) :=
    PanThreeSample.isProbability P.rate P.rate_locallyIntegrable P.rate_nonnegative P.clock_diverges
  let : IsProbabilityMeasure (μ.map Prod.fst) :=
    inferInstance
  let : IsProbabilityMeasure ((PanThreeSample.law P.rate).map Prod.fst) :=
    inferInstance
  have hpos (ν : Measure (ℝ × ℝ)) (hν : ∀ᵐ p ∂ν, 0 < p.1 ∧ p.1 < p.2) :
      ∀ᵐ t ∂ν.map Prod.fst, 0 < t := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Ioi).mpr
    filter_upwards [hν] with p hp
    exact hp.1
  apply positive_measure_eq_of_prefix _ _ (hpos μ ho)
    (hpos _ (PanThreeSample.law_ordered_support P.rate))
  intro t ht
  have h1 := hm t ht
  have h2 := P.pan_matches t ht
  unfold firstSurvival at h1 h2
  linarith

end FirstSurvivalProfile
end Rhone.Statistics.Identifiability.ThreeSampleMembership
