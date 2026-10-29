/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingUnrestrictedClassification
public import Rhone.Statistics.Identifiability.ThreeTimeVaryingCountLaw

/-! # Full unfolded product-Poisson counts of the unconditioned finite genealogy component -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling

def durationLaw (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (law ρ k c q).map PanThreeSample.toDurations

lemma law_ordered_support (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) :
    ∀ᵐ p ∂law ρ k c q, 0 < p.1 ∧ p.1 < p.2 :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem upperWedge_open.measurableSet)

lemma durationLaw_nonnegative (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) :
    FiniteSiteObservation.NonnegativeTimes (durationLaw ρ k c q) := by
  apply (ae_map_iff PanThreeSample.measurable_toDurations.aemeasurable
    (show MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
  filter_upwards [law_ordered_support ρ k c q] with p hp
  exact ⟨hp.1.le, sub_nonneg.mpr hp.2.le⟩

lemma recover_ordered_law (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) :
    (durationLaw ρ k c q).map PanThreeSample.toOrdered = law ρ k c q := by
  rw [durationLaw, Measure.map_map PanThreeSample.measurable_toOrdered
    PanThreeSample.measurable_toDurations]
  have he : PanThreeSample.toOrdered ∘ PanThreeSample.toDurations = id :=
    funext PanThreeSample.toOrdered_toDurations
  rw [he, Measure.map_id]

def countLaw (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (mutationRate : ℝ) : Measure (ℕ × ℕ) :=
  ThreeSampleCounts.law mutationRate (durationLaw ρ k c q)

lemma countLaw_eq_pan_iff_law_eq (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    {mutationRate : ℝ} (hm : 0 < mutationRate)
    (rate : ℝ → ℝ) (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    countLaw ρ k c q mutationRate = PanThreeSample.countLaw mutationRate rate ↔
      law ρ k c q = PanThreeSample.law rate := by
  constructor
  · intro he
    let : IsFiniteMeasure (law ρ k c q) := law_isFinite ρ k c q hρ hρsum hc hq hcn hqn
    let : IsFiniteMeasure (durationLaw ρ k c q) := by unfold durationLaw; infer_instance
    let : IsProbabilityMeasure (PanThreeSample.durationLaw rate) :=
      PanThreeSample.durationLaw_probability_halfLine rate hr hn htail
    have hd := ThreeSampleCounts.law_injective _ _ (durationLaw_nonnegative ρ k c q)
      (PanThreeSample.durationLaw_nonnegative rate) hm he
    have h := congrArg (Measure.map PanThreeSample.toOrdered) hd
    simpa only [recover_ordered_law, PanThreeSample.recover_ordered_law] using h
  · intro he
    simp only [countLaw, durationLaw, PanThreeSample.countLaw, PanThreeSample.durationLaw, he]

end Rhone.Statistics.Identifiability.ThreeSampling
