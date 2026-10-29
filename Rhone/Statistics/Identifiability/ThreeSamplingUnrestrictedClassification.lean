/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingUnrestrictedRigidity
public import Rhone.Statistics.Identifiability.ThreeSamplingZeroMigration
public import Rhone.Statistics.Identifiability.ThreeIntegrableHalfLine

/-! # Complete proper-pan membership for locally-L1 symmetric-island three-sample time laws -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling.Unrestricted

lemma equal_law_coalescence_clock_diverges (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law ρ k c q = PanThreeSample.law rate) :
    Tendsto (integratedClock c) atTop atTop := by
  have hrate := equal_law_rate_ratio_ae ρ k c q hρ hρsum hc hq hcn hqn rate hr hn htail he
  apply tendsto_atTop_mono' atTop _ htail
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  apply intervalIntegral.integral_mono_ae_restrict ht
    (locallyIntegrable_interval rate hr 0 t) (locallyIntegrable_interval c hc 0 t)
  change ∀ᵐ u ∂volume.restrict (Icc 0 t), rate u ≤ c u
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hrate, hcn] with u hu hcu hmem
  rw [hu hmem.1, rateRatio, max_eq_left hmem.1]
  exact mul_le_of_le_one_right (hcu hmem.1)
    (normalized_coordinates_bounds ρ k c q hρ hρsum hc hq hqn hmem.1).1.2

theorem pan_representable_iff (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧ Tendsto (integrablePanClock rate) atTop atTop ∧
      law ρ k c q = PanThreeSample.law rate) ↔
    (ρ = Pi.single 0 1 ∧ (∀ᵐ t, 0 ≤ t → q t = 0) ∧
      Tendsto (integrablePanClock c) atTop atTop) := by
  constructor
  · rintro ⟨rate, hr, hn, htail, he⟩
    let r := PanThreeSample.nonnegativeRepresentative rate
    have hr' := PanThreeSample.representative_locallyIntegrable hr
    have hn' := PanThreeSample.representative_nonneg rate
    have ht' := PanThreeSample.representative_clock_diverges hn htail
    have he' : law ρ k c q = PanThreeSample.law r :=
      he.trans (PanThreeSample.law_congr_halfLine_ae (PanThreeSample.representative_eq_ae hn))
    have hrig := equal_law_forces_initial_and_migration ρ k c q hρ hρsum hc hq hcn hqn
      r hr' hn' ht' he'
    have hdiv := equal_law_coalescence_clock_diverges ρ k c q hρ hρsum hc hq hcn hqn
      r hr' hn' ht' he'
    refine ⟨hrig.1, hrig.2, hdiv.congr' ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact PanThreeSample.clock_eq_halfLine c ht
  · rintro ⟨hinit, hzero, hclock⟩
    refine ⟨c, hc.locallyIntegrableOn (Ici 0), hcn, hclock, ?_⟩
    have he := law_zero_migration ρ k c q (hρ 0) hc hq hzero
    rw [hinit] at he ⊢
    simpa only [Pi.single_eq_same, ENNReal.ofReal_one, one_smul] using he

lemma clock_zeroExtension (c : ℝ → ℝ) :
    integrablePanClock (panZeroExtension c) = integrablePanClock c := by
  funext t
  simp only [integrablePanClock, panZeroExtension, indicator_indicator, inter_self]

theorem halfLine_pan_representable_iff (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrableOn c (Ici 0) volume) (hq : LocallyIntegrableOn q (Ici 0) volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧ Tendsto (integrablePanClock rate) atTop atTop ∧
      law ρ k (panZeroExtension c) (panZeroExtension q) = PanThreeSample.law rate) ↔
    (ρ = Pi.single 0 1 ∧ (∀ᵐ t, 0 ≤ t → q t = 0) ∧
      Tendsto (integrablePanClock c) atTop atTop) := by
  rw [pan_representable_iff ρ k (panZeroExtension c) (panZeroExtension q) hρ hρsum
    (panZeroExtension_locallyIntegrable hc) (panZeroExtension_locallyIntegrable hq)
    (ThreeIntegrable.extension_nonnegative_ae c hcn)
    (ThreeIntegrable.extension_nonnegative_ae q hqn), clock_zeroExtension]
  exact and_congr_right fun _ => and_congr_left fun _ => ThreeIntegrable.extension_ae_zero_iff q

end Rhone.Statistics.Identifiability.ThreeSampling.Unrestricted
