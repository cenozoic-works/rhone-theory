/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePhaseSurvivalProfile

/-! # Exact pan-membership and observable witnesses for arbitrary finite locally-L1 histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.IntegrablePhase.History
open ThreeSampleMembership ThreeSampleCDF
variable {n m : ℕ}

def DensityIdentity (M : History n m) : Prop :=
  M.density =ᵐ[planeVolume.restrict upperWedge]
    (fun p => 3 * M.u p.1 * M.d p.1 * M.d p.2)

theorem pan_representable_iff_density_identity (M : History n m) [IsProbabilityMeasure M.law] :
    PanRepresentable M.law ↔ M.DensityIdentity := by
  have he := M.profile.pan_representable_iff_density_ae M.density
    M.density_aemeasurable.restrict M.density_nonnegative_ae M.profile_matches
  unfold RegularPairSurvival.candidateDensity at he
  simpa only [law, DensityIdentity, profile] using he

lemma ordered_support (M : History n m) : ∀ᵐ p ∂M.law, 0 < p.1 ∧ p.1 < p.2 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem upperWedge_open.measurableSet)

lemma first_survival_proper (M : History n m) [IsProbabilityMeasure M.law] :
    Tendsto (IntegrableWeightedExit.survival M.A M.α 0) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (M.law.map Prod.fst) :=
    inferInstance
  have hp : ∀ᵐ t ∂M.law.map Prod.fst, 0 < t := by
    rw [M.first_marginal]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  apply (positive_probability_survival_tendsto_zero _ hp).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [M.first_marginal, IntegrableWeightedExit.real_Ioc M.A M.α M.A_integrable
    M.A_metzler M.A_rows M.α_nonnegative ht, M.α_sum]
  ring

def firstProfile (M : History n m) [IsProbabilityMeasure M.law] : FirstSurvivalProfile where
  survival := IntegrableWeightedExit.survival M.A M.α 0
  density := IntegrableWeightedExit.density M.A M.α 0
  continuous_survival := IntegrableWeightedExit.survival_continuous M.A M.α M.A_integrable 0
  initial := by rw [IntegrableWeightedExit.survival_initial M.A M.α M.A_integrable, M.α_sum]
  positive := fun _ ht => IntegrableWeightedExit.survival_positive M.A M.α M.A_integrable
    M.A_metzler M.α_nonnegative M.α_sum (le_refl (0 : ℝ)) ht
  ac := fun T _ => IntegrableWeightedExit.survival_ac M.A M.α M.A_integrable 0 0 T
  density_locallyIntegrable :=
    (IntegrableWeightedExit.density_locallyIntegrable M.A M.α M.A_integrable 0)
      |>.locallyIntegrableOn _
  density_nonnegative := IntegrableWeightedExit.density_nonnegative_ae M.A M.α M.A_integrable
    M.A_metzler M.A_rows M.α_nonnegative (le_refl (0 : ℝ))
  derivative_ae := by
    filter_upwards [IntegrableWeightedExit.survival_derivative_ae M.A M.α M.A_integrable 0]
      with t ht _
    exact ht
  proper := M.first_survival_proper

lemma firstProfile_matches (M : History n m) [IsProbabilityMeasure M.law] :
    M.firstProfile.Matches M.law := by
  intro t ht
  unfold firstSurvival
  rw [M.first_marginal, IntegrableWeightedExit.real_Ioc M.A M.α M.A_integrable
    M.A_metzler M.A_rows M.α_nonnegative ht, M.α_sum]
  change 1 - (1 - IntegrableWeightedExit.survival M.A M.α 0 t) =
    IntegrableWeightedExit.survival M.A M.α 0 t
  ring

theorem pan_representable_iff_rootFreeStatistic_zero (M : History n m)
    [IsProbabilityMeasure M.law] :
    PanRepresentable M.law ↔ ∀ s t : ℝ, 0 ≤ s → s ≤ t → rootFreeStatistic M.law s t = 0 := by
  rw [pan_representable_iff_regular_and_polynomial M.law]
  exact ⟨fun h => h.2.2, fun h => ⟨M.ordered_support, ⟨M.firstProfile, M.firstProfile_matches⟩, h⟩⟩

theorem exists_rootFreeStatistic_ne_zero (M : History n m) [IsProbabilityMeasure M.law]
    (hbad : ¬M.DensityIdentity) :
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ rootFreeStatistic M.law s t ≠ 0 := by
  have hp := mt M.pan_representable_iff_density_identity.mp hbad
  have hw := mt M.pan_representable_iff_rootFreeStatistic_zero.mpr hp
  simpa only [not_forall, exists_prop] using hw

theorem pan_representable_iff_mass_and_density_identity (M : History n m) :
    PanRepresentable M.law ↔ M.law univ = 1 ∧ M.DensityIdentity := by
  constructor
  · intro hp
    obtain ⟨rate, hr, hn, ht, he⟩ := hp
    have he' := he.trans
      (PanThreeSample.law_congr_halfLine_ae (PanThreeSample.representative_eq_ae hn))
    have hprob : IsProbabilityMeasure M.law := by
      rw [he']
      exact PanThreeSample.isProbability _ (PanThreeSample.representative_locallyIntegrable hr)
        (PanThreeSample.representative_nonneg rate)
        (PanThreeSample.representative_clock_diverges hn ht)
    let := hprob
    exact ⟨measure_univ, M.pan_representable_iff_density_identity.mp ⟨rate, hr, hn, ht, he⟩⟩
  · rintro ⟨hmass, hd⟩
    let : IsProbabilityMeasure M.law := ⟨hmass⟩
    exact M.pan_representable_iff_density_identity.mpr hd

end Rhone.Statistics.Identifiability.IntegrablePhase.History
