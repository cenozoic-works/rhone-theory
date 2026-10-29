/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseMembership

/-! # A finite event-probability witness for every non-pan proper finite two-stage model -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.FinitePhase.Model
open ThreeSampleMembership ThreeSampleCDF
variable {n m : ℕ}

lemma ordered_support (M : Model n m) : ∀ᵐ p ∂M.law, 0 < p.1 ∧ p.1 < p.2 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem upperWedge_open.measurableSet)

lemma first_survival_proper (M : Model n m) [IsProbabilityMeasure M.law] :
    Tendsto (WeightedExit.survival M.A M.α) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (M.law.map Prod.fst) :=
    inferInstance
  have hp : ∀ᵐ t ∂M.law.map Prod.fst, 0 < t := by
    rw [M.first_marginal]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  apply (positive_probability_survival_tendsto_zero _ hp).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [M.first_marginal, WeightedExit.real_Ioc M.A M.α M.A_metzler M.A_rows
    M.α_nonnegative ht, M.α_sum]
  ring

def firstProfile (M : Model n m) [IsProbabilityMeasure M.law] : FirstSurvivalProfile where
  survival := WeightedExit.survival M.A M.α
  density := WeightedExit.density M.A M.α
  continuous_survival := (WeightedExit.survival_contDiff M.A M.α).continuous
  initial := by simp [WeightedExit.survival, M.α_sum]
  positive := fun _ ht => WeightedExit.survival_positive M.A M.α M.A_metzler
    M.α_nonnegative M.α_sum ht
  ac := fun _ _ =>
    (WeightedExit.survival_contDiff M.A M.α).contDiffOn.absolutelyContinuousOnInterval
  density_locallyIntegrable :=
    (WeightedExit.density_continuous M.A M.α).locallyIntegrable.locallyIntegrableOn _
  density_nonnegative := ae_of_all _ fun _ ht =>
    WeightedExit.density_nonnegative M.A M.α M.A_metzler M.A_rows M.α_nonnegative ht
  derivative_ae := ae_of_all _ fun t _ => WeightedExit.survival_derivative M.A M.α t
  proper := M.first_survival_proper

lemma firstProfile_matches (M : Model n m) [IsProbabilityMeasure M.law] :
    M.firstProfile.Matches M.law := by
  intro t ht
  unfold firstSurvival
  rw [M.first_marginal, WeightedExit.real_Ioc M.A M.α M.A_metzler M.A_rows
    M.α_nonnegative ht, M.α_sum]
  change 1 - (1 - WeightedExit.survival M.A M.α t) = WeightedExit.survival M.A M.α t
  ring

variable [NeZero n] [NeZero m]

theorem certificate_iff_rootFreeStatistic_zero (M : Model n m) [IsProbabilityMeasure M.law] :
    M.Certificate ↔ ∀ s t : ℝ, 0 ≤ s → s ≤ t → rootFreeStatistic M.law s t = 0 := by
  rw [← M.pan_representable_iff_certificate,
    pan_representable_iff_regular_and_polynomial M.law]
  exact ⟨fun h => h.2.2, fun h => ⟨M.ordered_support, ⟨M.firstProfile, M.firstProfile_matches⟩, h⟩⟩

theorem exists_rootFreeStatistic_ne_zero (M : Model n m) [IsProbabilityMeasure M.law]
    (hc : ¬M.Certificate) : ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ rootFreeStatistic M.law s t ≠ 0 := by
  have h := mt M.certificate_iff_rootFreeStatistic_zero.mpr hc
  simpa only [not_forall, exists_prop] using h

end Rhone.Statistics.Identifiability.FinitePhase.Model
