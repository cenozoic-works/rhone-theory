/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingDuration
public import Rhone.Statistics.Identifiability.ThreeSampleCountObservation

/-! # Full unfolded singleton/doubleton counts preserve the continuous-island classification -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

def countLaw (k : ℕ) (c q : ℝ → ℝ) (mutationRate : ℝ) : Measure (ℕ × ℕ) :=
  ThreeSampleCounts.law mutationRate (durationLaw k c q)

lemma countLaw_probability (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {mutationRate : ℝ} (hm : 0 ≤ mutationRate) :
    IsProbabilityMeasure (countLaw k c q mutationRate) := by
  let : IsProbabilityMeasure (durationLaw k c q) :=
    durationLaw_probability k c q hc hq hcn hqn hproper
  exact ThreeSampleCounts.law_isProbability _ (durationLaw_nonnegative k c q) hm

theorem countLaw_eq_pan_iff_law_eq (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
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
    have hd := ThreeSampleCounts.law_injective _ _ (durationLaw_nonnegative k c q)
      (PanThreeSample.durationLaw_nonnegative rate) hm he
    have h := congrArg (Measure.map PanThreeSample.toOrdered) hd
    simpa only [recover_ordered_law, PanThreeSample.recover_ordered_law] using h
  · intro he
    simp only [countLaw, durationLaw, PanThreeSample.countLaw, PanThreeSample.durationLaw, he]

theorem counts_pan_representable_iff_zero_migration (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {mutationRate : ℝ} (hm : 0 < mutationRate) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧
      Tendsto (integrablePanClock rate) atTop atTop ∧
      countLaw k c q mutationRate = PanThreeSample.countLaw mutationRate rate) ↔
        (∀ t, 0 ≤ t → q t = 0) := by
  rw [← pan_representable_iff_zero_migration k c q hc hq hcn hqn hproper]
  constructor
  · rintro ⟨rate, hr, hn, htail, he⟩
    exact ⟨rate, hr, hn, htail,
      (countLaw_eq_pan_iff_law_eq k c q hc hq hcn hqn hproper hm rate hr hn htail).mp he⟩
  · rintro ⟨rate, hr, hn, htail, he⟩
    exact ⟨rate, hr, hn, htail,
      (countLaw_eq_pan_iff_law_eq k c q hc hq hcn hqn hproper hm rate hr hn htail).mpr he⟩

theorem countLaw_ne_pan_of_nonzero_migration (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    (hMigration : ∃ t, 0 ≤ t ∧ 0 < q t) {mutationRate : ℝ} (hm : 0 < mutationRate)
    (rate : ℝ → ℝ) (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    countLaw k c q mutationRate ≠ PanThreeSample.countLaw mutationRate rate := by
  intro he
  exact law_ne_pan_of_nonzero_migration k c q hc hq hcn hqn hproper hMigration rate hr hn htail
    ((countLaw_eq_pan_iff_law_eq k c q hc hq hcn hqn hproper hm rate hr hn htail).mp he)

end Rhone.Statistics.Identifiability.ThreeTimeVarying
