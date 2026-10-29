/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableZeroMigration
public import Rhone.Statistics.Identifiability.IntegrableNonzeroExposure
public import Rhone.Statistics.Identifiability.ThreeTimeVaryingDuration

/-! # Complete proper symmetric-island classification for locally integrable source histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

theorem pan_representable_iff_zero_migration_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧
      Tendsto (integrablePanClock rate) atTop atTop ∧
      law k c q = PanThreeSample.law rate) ↔ (∀ᵐ t, 0 ≤ t → q t = 0) := by
  constructor
  · rintro ⟨rate, hr, hn, htail, he⟩
    by_contra hzero
    obtain ⟨A, hA, hQ⟩ :=
      IntegrableExposure.exists_positive_exposure_of_not_ae_zero q hq hqn hzero
    exact law_ne_pan_of_positive_migration_halfLine k c q hc hq hcn hqn hproper hA hQ
      rate hr hn htail he
  · intro hzero
    have hdiv := PairIntegrable.coalescence_clock_diverges k c q hc hq hcn hqn hproper
    have he : integratedClock c =ᶠ[atTop] integrablePanClock c := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact PanThreeSample.clock_eq_halfLine c ht
    exact ⟨c, hc.locallyIntegrableOn (Ici 0), hcn, hdiv.congr' he,
      law_zero_migration_halfLine_ae k c q hc hq hzero⟩

lemma law_probability (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    IsProbabilityMeasure (law k c q) := by
  by_cases hz : ∀ᵐ t, 0 ≤ t → q t = 0
  · obtain ⟨rate, hr, hn, htail, he⟩ :=
      (pan_representable_iff_zero_migration_ae k c q hc hq hcn hqn hproper).mpr hz
    rw [he]
    exact PanThreeSample.law_probability_halfLine rate hr hn htail
  · obtain ⟨A, hA, hQ⟩ :=
      IntegrableExposure.exists_positive_exposure_of_not_ae_zero q hq hqn hz
    exact law_probability_initial_proper k c q hc hq hcn hqn hproper hA hQ

end Rhone.Statistics.Identifiability.ThreeIntegrable
