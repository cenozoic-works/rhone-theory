/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePhaseFirstDomination
public import Rhone.Statistics.Identifiability.RegularPairSurvivalMembership
public import Rhone.Statistics.Identifiability.PositiveSurvivalTail

/-! # The weighted-survival profile of an arbitrary proper finite L1 history -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.IntegrablePhase.History
open ThreeSampleMembership
variable {n m : ℕ}

def u (M : History n m) (t : ℝ) : ℝ :=
  (1/3 : ℝ) * IntegrableWeightedExit.survival M.A M.α 0 t +
    (2/3 : ℝ) * IntegrableWeightedExit.survival M.N M.γ 0 t

def d (M : History n m) (t : ℝ) : ℝ :=
  -((1/3 : ℝ) * IntegrableWeightedExit.density M.A M.α 0 t +
    (2/3 : ℝ) * IntegrableWeightedExit.density M.N M.γ 0 t)

lemma u_continuous (M : History n m) : Continuous M.u :=
  ((IntegrableWeightedExit.survival_continuous M.A M.α M.A_integrable 0).const_mul (1/3)).add
    ((IntegrableWeightedExit.survival_continuous M.N M.γ M.N_integrable 0).const_mul (2/3))

lemma u_ac (M : History n m) (a b : ℝ) : AbsolutelyContinuousOnInterval M.u a b := by
  exact ((IntegrableWeightedExit.survival_ac M.A M.α M.A_integrable 0 a b).const_mul (1/3)).add
    ((IntegrableWeightedExit.survival_ac M.N M.γ M.N_integrable 0 a b).const_mul (2/3))

lemma d_locallyIntegrable (M : History n m) : LocallyIntegrable M.d volume := by
  have hA := (IntegrableWeightedExit.density_locallyIntegrable M.A M.α M.A_integrable 0).smul
    (1/3 : ℝ)
  have hN := (IntegrableWeightedExit.density_locallyIntegrable M.N M.γ M.N_integrable 0).smul
    (2/3 : ℝ)
  convert! (hA.add hN).neg using 1

lemma u_derivative_ae (M : History n m) : ∀ᵐ t, HasDerivAt M.u (M.d t) t := by
  filter_upwards [IntegrableWeightedExit.survival_derivative_ae M.A M.α M.A_integrable 0,
    IntegrableWeightedExit.survival_derivative_ae M.N M.γ M.N_integrable 0] with t hA hN
  convert! (hA.const_mul (1/3 : ℝ)).add (hN.const_mul (2/3 : ℝ)) using 1
  unfold d
  ring

lemma u_initial (M : History n m) : M.u 0 = 1 := by
  simp only [u, IntegrableWeightedExit.survival_initial M.A M.α M.A_integrable,
    IntegrableWeightedExit.survival_initial M.N M.γ M.N_integrable, M.α_sum, M.γ_sum]
  norm_num

lemma u_positive (M : History n m) {t : ℝ} (ht : 0 ≤ t) : 0 < M.u t := by
  have hp := IntegrableWeightedExit.survival_positive M.A M.α M.A_integrable M.A_metzler
    M.α_nonnegative M.α_sum (le_refl (0 : ℝ)) ht
  have hn := IntegrableWeightedExit.survival_nonnegative M.N M.γ M.N_integrable M.N_metzler
    M.γ_nonnegative (le_refl (0 : ℝ)) ht
  unfold u
  linarith

lemma d_nonpositive_ae (M : History n m) : ∀ᵐ t, 0 ≤ t → M.d t ≤ 0 := by
  filter_upwards [IntegrableWeightedExit.density_nonnegative_ae M.A M.α M.A_integrable
    M.A_metzler M.A_rows M.α_nonnegative (le_refl (0 : ℝ)),
    IntegrableWeightedExit.density_nonnegative_ae M.N M.γ M.N_integrable
      M.N_metzler M.N_rows M.γ_nonnegative (le_refl (0 : ℝ))] with t hA hN ht
  have ha := hA ht
  have hn := hN ht
  unfold d
  linarith

lemma weighted_survival_eq (M : History n m) [IsProbabilityMeasure M.law] :
    ∀ t, 0 ≤ t → weightedSurvival M.law t = M.u t := by
  intro t ht
  rw [weightedSurvival, M.first_marginal, M.root_marginal,
    IntegrableWeightedExit.real_Ioc M.A M.α M.A_integrable M.A_metzler M.A_rows M.α_nonnegative ht,
    IntegrableWeightedExit.real_Ioc M.N M.γ M.N_integrable M.N_metzler M.N_rows M.γ_nonnegative ht,
    M.α_sum, M.γ_sum]
  unfold u
  ring

lemma u_proper (M : History n m) [IsProbabilityMeasure M.law] : Tendsto M.u atTop (𝓝 0) := by
  let : IsProbabilityMeasure (M.law.map Prod.fst) :=
    inferInstance
  let : IsProbabilityMeasure (M.law.map Prod.snd) :=
    inferInstance
  have hp1 : ∀ᵐ t ∂M.law.map Prod.fst, 0 < t := by
    rw [M.first_marginal]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hp2 : ∀ᵐ t ∂M.law.map Prod.snd, 0 < t := by
    rw [M.root_marginal]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have ht := ((positive_probability_survival_tendsto_zero _ hp1).const_mul (1/3 : ℝ)).add
    ((positive_probability_survival_tendsto_zero _ hp2).const_mul (2/3 : ℝ))
  have hw : Tendsto (weightedSurvival M.law) atTop (𝓝 0) := by
    unfold weightedSurvival
    simpa using ht
  apply hw.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht0
  exact M.weighted_survival_eq t ht0

def profile (M : History n m) [IsProbabilityMeasure M.law] : RegularPairSurvival where
  u := M.u
  d := M.d
  continuous_u := M.u_continuous
  locallyIntegrable_d := M.d_locallyIntegrable
  ac := fun T _ => M.u_ac 0 T
  derivative_ae := by filter_upwards [M.u_derivative_ae] with t ht _; exact ht
  initial := M.u_initial
  positive := fun _ ht => M.u_positive ht
  decreasing_ae := M.d_nonpositive_ae
  proper := M.u_proper

lemma profile_matches (M : History n m) [IsProbabilityMeasure M.law] :
    M.profile.Matches M.law := M.weighted_survival_eq

end Rhone.Statistics.Identifiability.IntegrablePhase.History
