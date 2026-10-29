/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingUnrestrictedDensity
public import Rhone.Statistics.Identifiability.ThreeSamplingInitialRowTraceRigidity
public import Rhone.Statistics.Identifiability.WeightedContinuousTrace

/-! # Equal proper pan laws force arbitrary-initial island sources to be unstructured -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling.Unrestricted

lemma equal_law_normalized_trace (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law ρ k c q = PanThreeSample.law rate) :
    ∀ᵐ t, 0 ≤ t → 0 < c t → normalizedY ρ k c q t = (normalizedX ρ k c q t) ^ 2 := by
  have htrace := weighted_continuous_upper_trace_ae c hc (jointKernel ρ k c q)
    (panNormalizedKernel ρ k c q rate) (jointKernel_continuous ρ k c q hc hq)
    (panNormalizedKernel_continuous ρ k c q rate hρ hρsum hc hq hqn hr)
    (equal_law_weighted_kernel_ae ρ k c q hρ hρsum hc hq hcn hqn rate hr hn htail he)
  filter_upwards [htrace, volume.ae_ne (0 : ℝ)] with t ht htne ht0 hct
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
  have hT := ht htpos hct.ne'
  have hS := equal_law_survival ρ k c q hρ hρsum hc hq hcn hqn
    rate hr hn htail he ht0
  have hExp : Real.exp (-2 * integratedClock rate t - integratedClock rate t) =
      survival ρ k c q t := by
    rw [hS]
    congr 1
    ring
  rw [jointKernel_trace ρ k c q hc hq] at hT
  change 3 * preRow ρ k c q t 0 =
    3 * rateRatio ρ k c q t * rateRatio ρ k c q t *
      Real.exp (-2 * integratedClock rate t - integratedClock rate t) at hT
  rw [hExp, rateRatio, max_eq_left ht0] at hT
  change preRow ρ k c q t 0 / survival ρ k c q t = _
  apply (div_eq_iff (survival_positive ρ k c q hρ hρsum hc hq hqn ht0).ne').mpr
  nlinarith only [hT]

theorem equal_law_forces_initial_and_migration (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law ρ k c q = PanThreeSample.law rate) :
    ρ = Pi.single 0 1 ∧ (∀ᵐ t, 0 ≤ t → q t = 0) := by
  have hrate := equal_law_rate_ratio_ae ρ k c q hρ hρsum hc hq hcn hqn
    rate hr hn htail he
  apply trace_rigidity ρ k c q (fun t => 3 * integratedClock rate t)
    hρ hρsum hc hq hcn hqn
  · intro a b ha hab
    apply ((integratedClock_ac_zero rate hr b).mono ?_).const_mul 3
    rw [uIcc_of_le hab, uIcc_of_le (ha.trans hab)]
    exact Icc_subset_Icc ha le_rfl
  · filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hr, hrate] with t ht hrt ht0
    have hd : HasDerivAt (fun u => 3 * integratedClock rate u) (3 * rate t) t := by
      convert! (ht 0).const_mul (3 : ℝ) using 1
    simpa only [hrt ht0, rateRatio, max_eq_left ht0, mul_assoc] using hd
  · exact equal_law_normalized_trace ρ k c q hρ hρsum hc hq hcn hqn
      rate hr hn htail he
  · exact htail.const_mul_atTop (by norm_num : (0 : ℝ) < 3)

end Rhone.Statistics.Identifiability.ThreeSampling.Unrestricted
