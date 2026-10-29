/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingClassification

/-! # Proper duration laws, including the zero-migration boundary -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

namespace PanThreeSample
lemma law_probability_halfLine (rate : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    IsProbabilityMeasure (law rate) := by
  rw [law_congr_halfLine_ae (representative_eq_ae hn)]
  exact isProbability (nonnegativeRepresentative rate) (representative_locallyIntegrable hr)
    (representative_nonneg rate) (representative_clock_diverges hn htail)

lemma durationLaw_probability_halfLine (rate : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    IsProbabilityMeasure (durationLaw rate) := by
  let : IsProbabilityMeasure (law rate) := law_probability_halfLine rate hr hn htail
  unfold durationLaw
  exact inferInstance
end PanThreeSample

namespace ThreeTimeVarying
theorem law_probability (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    IsProbabilityMeasure (law k c q) := by
  by_cases hzero : ∀ t, 0 ≤ t → q t = 0
  · obtain ⟨rate, hr, hn, htail, he⟩ :=
      (pan_representable_iff_zero_migration k c q hc hq hcn hqn hproper).mpr hzero
    rw [he]
    exact PanThreeSample.law_probability_halfLine rate hr hn htail
  · push Not at hzero
    obtain ⟨t, ht, hqt⟩ := hzero
    have hp : 0 < q t := lt_of_le_of_ne (hqn t ht) (Ne.symm hqt)
    exact law_probability_initial_proper k c q hc hq hcn hqn hproper (by linarith : 0 ≤ t + 1)
      (positive_exposure_of_positive_rate q hq hqn ht hp)

def durationLaw (k : ℕ) (c q : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (law k c q).map PanThreeSample.toDurations

lemma law_ordered_support (k : ℕ) (c q : ℝ → ℝ) :
    ∀ᵐ p ∂law k c q, 0 < p.1 ∧ p.1 < p.2 :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem upperWedge_open.measurableSet)

lemma durationLaw_nonnegative (k : ℕ) (c q : ℝ → ℝ) :
    FiniteSiteObservation.NonnegativeTimes (durationLaw k c q) := by
  apply (ae_map_iff PanThreeSample.measurable_toDurations.aemeasurable
    (show MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
  filter_upwards [law_ordered_support k c q] with p hp
  exact ⟨hp.1.le, sub_nonneg.mpr hp.2.le⟩

lemma durationLaw_probability (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    IsProbabilityMeasure (durationLaw k c q) := by
  let : IsProbabilityMeasure (law k c q) := law_probability k c q hc hq hcn hqn hproper
  unfold durationLaw
  exact inferInstance

lemma recover_ordered_law (k : ℕ) (c q : ℝ → ℝ) :
    (durationLaw k c q).map PanThreeSample.toOrdered = law k c q := by
  rw [durationLaw, Measure.map_map PanThreeSample.measurable_toOrdered
    PanThreeSample.measurable_toDurations]
  have he : PanThreeSample.toOrdered ∘ PanThreeSample.toDurations = id :=
    funext PanThreeSample.toOrdered_toDurations
  rw [he, Measure.map_id]

end ThreeTimeVarying
end Rhone.Statistics.Identifiability
