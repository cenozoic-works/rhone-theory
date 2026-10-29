/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableDensityRecovery
public import Rhone.Statistics.Identifiability.ThreeIntegrableExhaustion
public import Rhone.Statistics.Identifiability.WeightedContinuousTrace

/-! # Locally L1 symmetric-island histories separate from every proper L1 pan history -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma kernel_witness_identity (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (t : ℝ) :
    3 * survival k c q t * jointKernel k c q (t,t) -
      (∑ i, preRow k c q t i * mergerWeight i)^2 = ThreeTimeVarying.witness k c q t := by
  rw [jointKernel_trace k c q hc hq]
  unfold ThreeTimeVarying.witness
  ring

theorem equal_law_witness_zero_on_coalescence (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law k c q = PanThreeSample.law rate) :
    ∀ᵐ t, 0 < t → c t ≠ 0 → ThreeTimeVarying.witness k c q t = 0 := by
  have htrace := weighted_continuous_upper_trace_ae c hc (jointKernel k c q)
    (panNormalizedKernel k c q rate) (jointKernel_continuous k c q hc hq)
    (panNormalizedKernel_continuous k c q rate hc hq hqn hr)
    (equal_law_weighted_kernel_ae k c q hc hq hcn hqn hpair rate hr hn htail he)
  filter_upwards [htrace] with t ht htpos hct
  have hT := ht htpos hct
  have hS := equal_law_survival k c q hc hq hcn hqn hpair rate hr hn htail he htpos.le
  have hExp : Real.exp (-2 * integratedClock rate t - integratedClock rate t) =
      survival k c q t := by
    rw [hS]
    congr 1
    ring
  have hρ := rateRatio_mul_survival k c q hc hq hqn htpos.le
  have hW := kernel_witness_identity k c q hc hq t
  rw [hT] at hW
  change 3 * survival k c q t *
    (3 * rateRatio k c q t * rateRatio k c q t *
      Real.exp (-2 * integratedClock rate t - integratedClock rate t)) -
      (∑ i, preRow k c q t i * mergerWeight i)^2 = _ at hW
  rw [hExp, ← hρ] at hW
  have hz : 3 * survival k c q t *
      (3 * rateRatio k c q t * rateRatio k c q t * survival k c q t) -
      (3 * rateRatio k c q t * survival k c q t)^2 = 0 := by ring
  rw [hz] at hW
  exact hW.symm

theorem law_ne_pan_of_positive_migration (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop) :
    law k c q ≠ PanThreeSample.law rate := by
  intro he
  have hpair := PairIntegrable.all_pair_tails_of_initial_proper k c q hc hq hqn hproper hA hQ
  have hzero := equal_law_witness_zero_on_coalescence k c q hc hq hcn hqn
    (fun s _ i => hpair s i) rate hr hn htail he
  obtain ⟨a, b, ha, hab, hC, hW⟩ :=
    exists_positive_witness_window_initial_proper k c q hc hq hcn hqn hproper hA hQ
  have hz : (∫ u in a..b, c u) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [hzero, volume.ae_ne b] with u hu hne hmem
    rw [uIoc_of_le hab.le] at hmem
    by_contra hcu
    have heq := hu (ha.trans_lt hmem.1) hcu
    exact (hW u ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩).ne' heq
  exact hC.ne' hz

theorem law_ne_pan_of_positive_migration_halfLine (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A)
    (rate : ℝ → ℝ) (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    law k c q ≠ PanThreeSample.law rate := by
  intro he
  apply law_ne_pan_of_positive_migration k c q hc hq hcn hqn hproper hA hQ
    (PanThreeSample.nonnegativeRepresentative rate)
    (PanThreeSample.representative_locallyIntegrable hr)
    (PanThreeSample.representative_nonneg rate)
    (PanThreeSample.representative_clock_diverges hn htail)
  exact he.trans (PanThreeSample.law_congr_halfLine_ae (PanThreeSample.representative_eq_ae hn))

end Rhone.Statistics.Identifiability.ThreeIntegrable
