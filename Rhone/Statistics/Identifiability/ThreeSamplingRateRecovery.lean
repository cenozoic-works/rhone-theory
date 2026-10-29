/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingJointLaw
public import Rhone.Statistics.Identifiability.ThreeIntegrableRateRecovery

/-! # First-law equality recovers the hazard for arbitrary initial sampling -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling

def rateRatio (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  normalizedX ρ k c q (max t 0)

lemma rateRatio_continuous (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) : Continuous (rateRatio ρ k c q) := by
  have hm : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  have hnum : Continuous (fun t => 3 * preRow ρ k c q t 0 + preRow ρ k c q t 1) :=
    (continuous_const.mul (preRow_continuous ρ k c q hc hq 0)).add
    (preRow_continuous ρ k c q hc hq 1)
  exact (hnum.comp hm).div
    (continuous_const.mul ((survival_continuous ρ k c q hc hq).comp hm))
    (fun t => mul_ne_zero (by norm_num)
      (survival_positive ρ k c q hρ hρsum hc hq hqn (le_max_right t 0)).ne')

lemma equal_law_survival (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law ρ k c q = PanThreeSample.law rate) {t : ℝ} (ht : 0 ≤ t) :
    survival ρ k c q t = Real.exp (-(3 * integratedClock rate t)) := by
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) he
  rw [law_first_marginal ρ k c q hρ hc hq hcn hqn hpair,
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
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law ρ k c q = PanThreeSample.law rate) :
    ∀ᵐ t, 0 ≤ t → rate t = c t * rateRatio ρ k c q t := by
  filter_upwards [survival_derivative_ae ρ k c q hc hq,
    LocallyIntegrable.ae_hasDerivAt_integral hr, volume.ae_ne (0 : ℝ)] with t hdS hH htne ht0
  have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
  have hs (u : ℝ) (hu : 0 ≤ u) :=
    equal_law_survival ρ k c q hρ hρsum hc hq hcn hqn hpair rate hr hn htail he hu
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

end Rhone.Statistics.Identifiability.ThreeSampling
