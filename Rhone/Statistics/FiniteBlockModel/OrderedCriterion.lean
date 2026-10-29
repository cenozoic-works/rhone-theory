/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.JointCriterion
public import Rhone.Statistics.Identifiability.ThreeSamplePanMembership

/-! # Separation criterion for the uniform-cherry lift of ordered merger times -/

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Rhone.Statistics.FiniteBlockModel
open WeakRegularSeparation CollapsedGenealogy Algebra.Identifiability MarkovChain.Identifiability
    Identifiability
open ThreeSampleMembership ThreeTipSites

def durations (μ : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  μ.map PanThreeSample.toDurations

instance durations_probability (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (durations μ) :=
  by change IsProbabilityMeasure (Measure.map _ _); infer_instance

theorem durations_injective : Function.Injective durations := by
  apply PanThreeSample.measurable_toDurations.measurableEmbedding _ |>.map_injective
  intro x y he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only [PanThreeSample.toDurations] at h1 h2
  exact Prod.ext h1 (by linarith)

theorem durations_first_marginal (μ : Measure (ℝ × ℝ)) :
    (durations μ).map Prod.fst = μ.map Prod.fst := by
  unfold durations
  rw [Measure.map_map measurable_fst PanThreeSample.measurable_toDurations]
  rfl

theorem ordered_uniformlySeparated_iff {k : ℝ} (hk : 0 < k)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (ho : ∀ᵐ p ∂μ, 0 < p.1 ∧ p.1 < p.2)
    (P : FirstSurvivalProfile) (hP : P.Matches μ) :
    UniformlySeparated k (uniformLift (durations μ)) ↔ ¬ PanRepresentable μ := by
  have hs : ∀ᵐ t ∂durations μ, 0 < t.1 ∧ 0 < t.2 := by
    apply (ae_map_iff PanThreeSample.measurable_toDurations.aemeasurable
      (show MeasurableSet {t : ℝ × ℝ | 0 < t.1 ∧ 0 < t.2} by measurability)).mpr
    filter_upwards [ho] with p hp
    exact ⟨hp.1, sub_pos.mpr hp.2⟩
  have hp : P.Matches (durations μ) := by
    intro t ht
    unfold ThreeSampleCDF.firstSurvival
    rw [durations_first_marginal]
    exact hP t ht
  rw [regular_profile_uniform_criterion hk (durations μ)
    (hs.mono fun _ h => ⟨h.1.le, h.2.le⟩) (hs.mono fun _ h => h.1) P hp]
  have he : durations μ = PanThreeSample.durationLaw P.rate ↔
      μ = PanThreeSample.law P.rate := durations_injective.eq_iff
  apply not_congr
  rw [he, eq_candidate_iff P μ ho hP, pan_representable_iff_regular_and_residual μ]
  exact ⟨fun h => ⟨ho, ⟨P, hP⟩, h⟩, fun h => h.2.2⟩

end Rhone.Statistics.FiniteBlockModel
