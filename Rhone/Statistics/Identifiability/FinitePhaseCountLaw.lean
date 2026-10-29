/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseAlgebraicMembership
public import Rhone.Statistics.Identifiability.ThreeSamplePanCountMass
public import Rhone.Statistics.Identifiability.ThreeTimeVaryingCountLaw

/-! # Full unfolded product-Poisson observations of finite homogeneous two-stage laws -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix
namespace Rhone.Statistics.Identifiability.FinitePhase.Model
variable {n m : ℕ}

lemma law_mass_le_one (M : Model n m) : M.law univ ≤ 1 := by
  have he : WeightedExit.law M.N M.γ univ = M.law univ := by
    rw [← M.root_marginal, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]
  rw [← he]
  exact WeightedExit.law_mass_le_one M.N M.γ M.N_metzler M.N_rows M.γ_nonnegative M.γ_sum

lemma law_isFinite (M : Model n m) : IsFiniteMeasure M.law :=
  ⟨M.law_mass_le_one.trans_lt (by simp)⟩

def durationLaw (M : Model n m) : Measure (ℝ × ℝ) := M.law.map PanThreeSample.toDurations

def countLaw (M : Model n m) (r : ℝ) : Measure (ℕ × ℕ) :=
  ThreeSampleCounts.law r M.durationLaw

lemma durationLaw_nonnegative (M : Model n m) :
    FiniteSiteObservation.NonnegativeTimes M.durationLaw := by
  apply (ae_map_iff PanThreeSample.measurable_toDurations.aemeasurable
    (show MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_const measurable_snd))).mpr
  filter_upwards [M.ordered_support] with p hp
  exact ⟨hp.1.le, sub_nonneg.mpr hp.2.le⟩

lemma recover_ordered_law (M : Model n m) :
    M.durationLaw.map PanThreeSample.toOrdered = M.law := by
  rw [durationLaw, Measure.map_map PanThreeSample.measurable_toOrdered
    PanThreeSample.measurable_toDurations]
  have he : PanThreeSample.toOrdered ∘ PanThreeSample.toDurations = id :=
    funext PanThreeSample.toOrdered_toDurations
  rw [he, Measure.map_id]

lemma countLaw_univ_eq (M : Model n m) {r : ℝ} (hr : 0 ≤ r) :
    M.countLaw r univ = M.law univ := by
  let : IsFiniteMeasure M.law := M.law_isFinite
  let : IsFiniteMeasure M.durationLaw := by unfold durationLaw; infer_instance
  let : IsFiniteMeasure (M.durationLaw.map ThreeSampleCounts.branches) := inferInstance
  rw [countLaw, ThreeSampleCounts.law,
    MixedPoisson.law_univ_eq _
      (ThreeSampleCounts.nonnegative_branch_law _ M.durationLaw_nonnegative) hr hr,
    Measure.map_apply ThreeSampleCounts.measurable_branches MeasurableSet.univ,
    preimage_univ, durationLaw,
    Measure.map_apply PanThreeSample.measurable_toDurations MeasurableSet.univ, preimage_univ]

lemma law_probability_of_countLaw_probability (M : Model n m) {r : ℝ} (hr : 0 ≤ r)
    [IsProbabilityMeasure (M.countLaw r)] : IsProbabilityMeasure M.law := by
  constructor
  rw [← M.countLaw_univ_eq hr, measure_univ]

lemma countLaw_probability (M : Model n m) [IsProbabilityMeasure M.law]
    {r : ℝ} (hr : 0 ≤ r) : IsProbabilityMeasure (M.countLaw r) := by
  let : IsProbabilityMeasure M.durationLaw :=
    by change IsProbabilityMeasure (Measure.map _ _); infer_instance
  exact ThreeSampleCounts.law_isProbability _ M.durationLaw_nonnegative hr

lemma countLaw_eq_pan_iff_law_eq (M : Model n m) {r : ℝ} (hr : 0 < r)
    (rate : ℝ → ℝ) (hc : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    M.countLaw r = PanThreeSample.countLaw r rate ↔ M.law = PanThreeSample.law rate := by
  constructor
  · intro he
    let : IsFiniteMeasure M.law := M.law_isFinite
    let : IsFiniteMeasure M.durationLaw := by unfold durationLaw; infer_instance
    let : IsProbabilityMeasure (PanThreeSample.durationLaw rate) :=
      PanThreeSample.durationLaw_probability_halfLine rate hc hn htail
    have hd := ThreeSampleCounts.law_injective _ _ M.durationLaw_nonnegative
      (PanThreeSample.durationLaw_nonnegative rate) hr he
    have h := congrArg (Measure.map PanThreeSample.toOrdered) hd
    simpa only [recover_ordered_law, PanThreeSample.recover_ordered_law] using h
  · intro he
    simp only [countLaw, durationLaw, PanThreeSample.countLaw, PanThreeSample.durationLaw, he]

variable [NeZero n] [NeZero m]

theorem counts_pan_representable_iff_finite_algebra (M : Model n m) {r : ℝ} (hr : 0 < r) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧ Tendsto (integrablePanClock rate) atTop atTop ∧
      M.countLaw r = PanThreeSample.countLaw r rate) ↔
    (∃ β : Fin (n + m) → ℝ, β ᵥ* M.N = M.γ) ∧ M.Certificate := by
  rw [← M.pan_representable_iff_finite_algebra]
  constructor
  · rintro ⟨rate, hc, hn, ht, he⟩
    exact ⟨rate, hc, hn, ht, (M.countLaw_eq_pan_iff_law_eq hr rate hc hn ht).mp he⟩
  · rintro ⟨rate, hc, hn, ht, he⟩
    exact ⟨rate, hc, hn, ht, (M.countLaw_eq_pan_iff_law_eq hr rate hc hn ht).mpr he⟩

end Rhone.Statistics.Identifiability.FinitePhase.Model
