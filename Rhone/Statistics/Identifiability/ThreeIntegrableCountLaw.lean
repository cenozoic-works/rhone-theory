/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableHalfLine
public import Rhone.Statistics.Identifiability.ThreeTimeVaryingCountLaw

/-! # Full unfolded mutation-count laws classify proper locally L1 symmetric islands -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma durationLaw_probability (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    IsProbabilityMeasure (durationLaw k c q) := by
  let : IsProbabilityMeasure (law k c q) := law_probability k c q hc hq hcn hqn hproper
  unfold durationLaw
  exact inferInstance

lemma countLaw_probability (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {mutationRate : ℝ} (hm : 0 ≤ mutationRate) :
    IsProbabilityMeasure (countLaw k c q mutationRate) := by
  let : IsProbabilityMeasure (durationLaw k c q) :=
    durationLaw_probability k c q hc hq hcn hqn hproper
  exact ThreeSampleCounts.law_isProbability _ (ThreeTimeVarying.durationLaw_nonnegative k c q) hm

lemma countLaw_eq_pan_iff_law_eq (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {mutationRate : ℝ} (hm : 0 < mutationRate)
    (rate : ℝ → ℝ) (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    countLaw k c q mutationRate = PanThreeSample.countLaw mutationRate rate ↔
      law k c q = PanThreeSample.law rate := by
  constructor
  · intro he
    let : IsProbabilityMeasure (durationLaw k c q) :=
      durationLaw_probability k c q hc hq hcn hqn hproper
    let : IsProbabilityMeasure (PanThreeSample.durationLaw rate) :=
      PanThreeSample.durationLaw_probability_halfLine rate hr hn htail
    have hd := ThreeSampleCounts.law_injective _ _ (ThreeTimeVarying.durationLaw_nonnegative k c q)
      (PanThreeSample.durationLaw_nonnegative rate) hm he
    have h := congrArg (Measure.map PanThreeSample.toOrdered) hd
    simpa only [ThreeTimeVarying.recover_ordered_law, PanThreeSample.recover_ordered_law] using h
  · intro he
    simp only [countLaw, durationLaw, PanThreeSample.countLaw, PanThreeSample.durationLaw, he]

theorem counts_pan_representable_iff_zero_migration_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {mutationRate : ℝ} (hm : 0 < mutationRate) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧
      Tendsto (integrablePanClock rate) atTop atTop ∧
      countLaw k c q mutationRate = PanThreeSample.countLaw mutationRate rate) ↔
        (∀ᵐ t, 0 ≤ t → q t = 0) := by
  rw [← pan_representable_iff_zero_migration_ae k c q hc hq hcn hqn hproper]
  constructor
  · rintro ⟨rate, hr, hn, htail, he⟩
    exact ⟨rate, hr, hn, htail,
      (countLaw_eq_pan_iff_law_eq k c q hc hq hcn hqn hproper hm rate hr hn htail).mp he⟩
  · rintro ⟨rate, hr, hn, htail, he⟩
    exact ⟨rate, hr, hn, htail,
      (countLaw_eq_pan_iff_law_eq k c q hc hq hcn hqn hproper hm rate hr hn htail).mpr he⟩

theorem halfLine_counts_pan_representable_iff_zero_migration_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrableOn c (Ici 0) volume) (hq : LocallyIntegrableOn q (Ici 0) volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k (panZeroExtension c) (panZeroExtension q) 0 0)
      atTop (𝓝 0)) {mutationRate : ℝ} (hm : 0 < mutationRate) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧ Tendsto (integrablePanClock rate) atTop atTop ∧
      countLaw k (panZeroExtension c) (panZeroExtension q) mutationRate =
        PanThreeSample.countLaw mutationRate rate) ↔ (∀ᵐ t, 0 ≤ t → q t = 0) :=
  (counts_pan_representable_iff_zero_migration_ae k (panZeroExtension c) (panZeroExtension q)
    (panZeroExtension_locallyIntegrable hc) (panZeroExtension_locallyIntegrable hq)
    (extension_nonnegative_ae c hcn) (extension_nonnegative_ae q hqn) hproper hm).trans
      (extension_ae_zero_iff q)

end Rhone.Statistics.Identifiability.ThreeIntegrable
