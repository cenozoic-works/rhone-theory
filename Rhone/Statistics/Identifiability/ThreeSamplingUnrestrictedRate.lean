/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingRateRecovery
public import Rhone.Statistics.Identifiability.ThreeSamplingMarginalDomination

/-! # Equal laws force equal survival and rate ratio for an unrestricted pan rate -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling.Unrestricted

lemma equal_law_survival (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law ρ k c q = PanThreeSample.law rate) {t : ℝ} (ht : 0 ≤ t) :
    survival ρ k c q t = Real.exp (-(3 * integratedClock rate t)) := by
  let : IsProbabilityMeasure (law ρ k c q) := by
    rw [he]
    exact PanThreeSample.isProbability rate hr hn htail
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) he
  rw [law_first_marginal_of_probability ρ k c q hρ hρsum hc hq hcn hqn,
    PanThreeSample.first_marginal rate hr hn htail] at hm
  have h3 : LocallyIntegrable (fun u => 3 * rate u) volume := by
    convert! hr.smul (3 : ℝ) using 1
  have hCDF := congrArg (fun μ : Measure ℝ => μ.real (Ioc 0 t)) hm
  rw [firstLaw_real_Ioc ρ k c q hρ hρsum hc hq hcn hqn ht,
    panPairLaw_real_Ioc _ h3 (fun u => mul_nonneg (by norm_num) (hn u)) ht,
    integratedClock_scale] at hCDF
  linarith

lemma equal_law_rate_ratio_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law ρ k c q = PanThreeSample.law rate) :
    ∀ᵐ t, 0 ≤ t → rate t = c t * rateRatio ρ k c q t := by
  filter_upwards [survival_derivative_ae ρ k c q hc hq,
    LocallyIntegrable.ae_hasDerivAt_integral hr, volume.ae_ne (0 : ℝ)] with t hdS hH htne ht0
  have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
  have hs (u : ℝ) (hu : 0 ≤ u) :=
    equal_law_survival ρ k c q hρ hρsum hc hq hcn hqn rate hr hn htail he hu
  have hEq : survival ρ k c q =ᶠ[𝓝 t] (fun u => Real.exp (-(3 * integratedClock rate u))) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact hs u hu.le
  have hclock : HasDerivAt (integratedClock rate) (rate t) t := hH 0
  have hd : HasDerivAt (fun u => Real.exp (-(3 * integratedClock rate u)))
      (-(3 * rate t) * Real.exp (-(3 * integratedClock rate t))) t := by
    convert! (hclock.const_mul (3 : ℝ)).neg.exp using 1
    simp only [Pi.neg_apply]
    ring
  have hederiv := hdS.unique (hd.congr_of_eventuallyEq hEq)
  rw [← hs t ht0] at hederiv
  have hpos := (survival_positive ρ k c q hρ hρsum hc hq hqn ht0).ne'
  simp only [rateRatio, normalizedX, max_eq_left ht0]
  field_simp
  nlinarith

end Rhone.Statistics.Identifiability.ThreeSampling.Unrestricted
