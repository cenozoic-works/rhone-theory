/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingCountLaw
public import Rhone.Statistics.Identifiability.ProfileFirstMarginal

/-! # Every proper island time law supplies the regular observed first-survival profile -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Rhone.Statistics.Identifiability.ThreeSampling

lemma survival_tendsto_zero_of_probability (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    [IsProbabilityMeasure (law ρ k c q)]
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    Tendsto (survival ρ k c q) atTop (𝓝 0) := by
  let ν := firstLaw ρ k c q
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    rw [← law_first_marginal_of_probability ρ k c q hρ hρsum hc hq hcn hqn]
    exact inferInstance
  have hpos : ∀ᵐ t ∂ν, 0 < t :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hlim := tendsto_measure_Iic_atTop ν
  rw [measure_univ] at hlim
  have hreal : Tendsto (fun t => ν.real (Iic t)) atTop (𝓝 1) := by
    simpa only [Measure.real, ENNReal.toReal_one, Function.comp_def] using
      (ENNReal.continuousAt_toReal (by simp : (1 : ℝ≥0∞) ≠ ∞)).tendsto.comp hlim
  have hsub : Tendsto (fun t => 1 - ν.real (Iic t)) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hreal
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [real_Iic_eq_Ioc_of_positive ν hpos t]
  have h := firstLaw_real_Ioc ρ k c q hρ hρsum hc hq hcn hqn ht
  change ν.real (Ioc 0 t) = 1 - survival ρ k c q t at h
  linarith

def sourceProfile (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    [IsProbabilityMeasure (law ρ k c q)]
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    ThreeSampleMembership.FirstSurvivalProfile where
  survival := survival ρ k c q
  density := firstDensity ρ k c q
  continuous_survival := survival_continuous ρ k c q hc hq
  initial := survival_initial ρ k c q hρsum hc hq
  positive := fun _ ht => survival_positive ρ k c q hρ hρsum hc hq hqn ht
  ac := fun T _ => survival_ac ρ k c q hc hq 0 T
  density_locallyIntegrable := (firstDensity_locallyIntegrable ρ k c q hc hq).locallyIntegrableOn _
  density_nonnegative := firstDensity_nonnegative_ae ρ k c q hρ hc hq hcn hqn
  derivative_ae := by
    filter_upwards [survival_derivative_ae ρ k c q hc hq] with t ht _
    simpa only [firstDensity, neg_mul] using ht
  proper := survival_tendsto_zero_of_probability ρ k c q hρ hρsum hc hq hcn hqn

lemma sourceProfile_matches (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    [IsProbabilityMeasure (law ρ k c q)]
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    (sourceProfile ρ k c q hρ hρsum hc hq hcn hqn).Matches (law ρ k c q) := by
  intro t ht
  change 1 - ((law ρ k c q).map Prod.fst).real (Ioc 0 t) = survival ρ k c q t
  rw [law_first_marginal_of_probability ρ k c q hρ hρsum hc hq hcn hqn,
    firstLaw_real_Ioc ρ k c q hρ hρsum hc hq hcn hqn ht]
  ring

end Rhone.Statistics.Identifiability.ThreeSampling
