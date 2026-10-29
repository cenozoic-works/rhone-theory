/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanFirstSurvivalProfile
public import Rhone.Statistics.Identifiability.OrderedPrefixTailUniqueness
public import Rhone.Statistics.Identifiability.ThreeSampleRootFreeLaw

/-! # A source-model-independent proper-pan membership criterion for three-sample time laws -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership
open ThreeSampleCDF

def PanRepresentable (μ : Measure (ℝ × ℝ)) : Prop :=
  ∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
    (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧ Tendsto (integrablePanClock rate) atTop atTop ∧
    μ = PanThreeSample.law rate

theorem eq_candidate_iff (P : FirstSurvivalProfile) (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] (ho : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 < p.2) (hm : P.Matches μ) :
    μ = PanThreeSample.law P.rate ↔
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → rectangleResidual μ s t = 0 := by
  constructor
  · intro he s t hs hst
    rw [he]
    exact pan_rectangleResidual_zero P.rate P.rate_locallyIntegrable
      P.rate_nonnegative P.clock_diverges hs hst
  · intro hzero
    let : IsProbabilityMeasure (PanThreeSample.law P.rate) :=
      PanThreeSample.isProbability P.rate P.rate_locallyIntegrable
        P.rate_nonnegative P.clock_diverges
    have hfirst := P.first_marginal_eq μ ho hm
    apply eq_of_ordered_prefix_tail μ _ ho (PanThreeSample.law_ordered_support P.rate) hfirst
    intro s t hs hst
    have h1 := hzero s t hs hst
    have h2 := pan_rectangleResidual_zero P.rate P.rate_locallyIntegrable
      P.rate_nonnegative P.clock_diverges hs hst
    unfold rectangleResidual clockRoot firstSurvival at h1 h2
    rw [hfirst] at h1
    linarith

lemma candidate_proper_halfLine (P : FirstSurvivalProfile) :
    Tendsto (integrablePanClock P.rate) atTop atTop := by
  apply P.clock_diverges.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact PanThreeSample.clock_eq_halfLine P.rate ht

theorem pan_representable_iff_regular_and_residual (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] :
    PanRepresentable μ ↔ (∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 < p.2) ∧
      (∃ P : FirstSurvivalProfile, P.Matches μ) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → rectangleResidual μ s t = 0) := by
  constructor
  · rintro ⟨rate, hr, hn, htail, he⟩
    let r := PanThreeSample.nonnegativeRepresentative rate
    have hr' := PanThreeSample.representative_locallyIntegrable hr
    have hn' := PanThreeSample.representative_nonneg rate
    have ht' := PanThreeSample.representative_clock_diverges hn htail
    have he' : μ = PanThreeSample.law r :=
      he.trans (PanThreeSample.law_congr_halfLine_ae (PanThreeSample.representative_eq_ae hn))
    refine ⟨?_, ⟨panProfile r hr' hn' ht', ?_⟩, ?_⟩
    · rw [he]
      exact PanThreeSample.law_ordered_support rate
    · rw [he']
      exact panProfile_matches r hr' hn' ht'
    · intro s t hs hst
      rw [he]
      exact pan_rectangleResidual_zero_halfLine rate hr hn htail hs hst
  · rintro ⟨ho, ⟨P, hm⟩, hzero⟩
    exact ⟨P.rate, P.rate_locallyIntegrable.locallyIntegrableOn _,
      ae_of_all _ (fun t _ => P.rate_nonnegative t), candidate_proper_halfLine P,
      (eq_candidate_iff P μ ho hm).mpr hzero⟩

theorem pan_representable_iff_regular_and_polynomial (μ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure μ] :
    PanRepresentable μ ↔ (∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 < p.2) ∧
      (∃ P : FirstSurvivalProfile, P.Matches μ) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → rootFreeStatistic μ s t = 0) := by
  rw [pan_representable_iff_regular_and_residual]
  simp only [rootFreeStatistic_zero_iff]

end Rhone.Statistics.Identifiability.ThreeSampleMembership
