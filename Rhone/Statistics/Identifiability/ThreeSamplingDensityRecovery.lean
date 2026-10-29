/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingRateRecovery

/-! # Recovery of the pan-normalized kernel from equal three-sample laws -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling

def panNormalizedKernel (ρ : State → ℝ) (k : ℕ) (c q rate : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  3 * rateRatio ρ k c q p.1 * rateRatio ρ k c q p.2 *
    Real.exp (-2 * integratedClock rate p.1 - integratedClock rate p.2)

lemma panNormalizedKernel_continuous (ρ : State → ℝ) (k : ℕ) (c q rate : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) (hr : LocallyIntegrable rate volume) :
    Continuous (panNormalizedKernel ρ k c q rate) := by
  have hρ := rateRatio_continuous ρ k c q hρ hρsum hc hq hqn
  have hH := integratedClock_continuous rate hr
  unfold panNormalizedKernel
  fun_prop

lemma jointDensity_nonnegative_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    ∀ᵐ p ∂planeVolume, p ∈ upperWedge → 0 ≤ jointDensity ρ k c q p := by
  have h1 : ∀ᵐ p ∂planeVolume, 0 ≤ p.1 → 0 ≤ c p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hcn
  have h2 : ∀ᵐ p ∂planeVolume, 0 ≤ p.2 → 0 ≤ c p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hcn
  filter_upwards [h1, h2] with p hp1 hp2 hp
  rw [jointDensity_factor]
  exact mul_nonneg (mul_nonneg (hp1 hp.1.le) (hp2 (hp.1.trans hp.2).le))
    (jointKernel_nonnegative ρ k c q hρ hc hq hqn hp)

lemma equal_law_weighted_kernel_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law ρ k c q = PanThreeSample.law rate) :
    ∀ᵐ p ∂planeVolume, 0 < p.1 → p.1 < p.2 →
      c p.1 * c p.2 * (jointKernel ρ k c q p - panNormalizedKernel ρ k c q rate p) = 0 := by
  have hmeasure := he
  unfold law PanThreeSample.law triangularDensityLaw at hmeasure
  have hENN := (withDensity_eq_iff_of_sigmaFinite
    (jointDensity_aemeasurable ρ k c q hc hq).ennreal_ofReal
    (PanThreeSample.density_aemeasurable rate hr).ennreal_ofReal).mp hmeasure
  have hpan (p : ℝ × ℝ) : 0 ≤ PanThreeSample.jointDensity rate p := by
    rw [PanThreeSample.jointDensity_exp]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hn p.1)) (hn p.2))
      (Real.exp_pos _).le
  have hreal : jointDensity ρ k c q =ᵐ[planeVolume.restrict upperWedge]
      PanThreeSample.jointDensity rate := by
    filter_upwards [hENN, (jointDensity_nonnegative_ae ρ k c q hρ hc hq hcn hqn).filter_mono
      (ae_mono Measure.restrict_le_self), ae_restrict_mem upperWedge_open.measurableSet]
      with p hp hnonneg hmem
    exact (ENNReal.ofReal_eq_ofReal_iff (hnonneg hmem) (hpan p)).mp hp
  have hglobal := (ae_restrict_iff' upperWedge_open.measurableSet).mp hreal
  have hrate := equal_law_rate_ratio_ae ρ k c q hρ hρsum hc hq hcn hqn hpair rate hr hn htail he
  have hr1 : ∀ᵐ p ∂planeVolume, 0 ≤ p.1 → rate p.1 = c p.1 * rateRatio ρ k c q p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hrate
  have hr2 : ∀ᵐ p ∂planeVolume, 0 ≤ p.2 → rate p.2 = c p.2 * rateRatio ρ k c q p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hrate
  filter_upwards [hglobal, hr1, hr2] with p hp hp1 hp2 hs hst
  calc
    _ = jointDensity ρ k c q p - PanThreeSample.jointDensity rate p := by
      rw [jointDensity_factor, PanThreeSample.jointDensity_exp,
        hp1 hs.le, hp2 (hs.trans hst).le]
      unfold panNormalizedKernel
      ring
    _ = 0 := sub_eq_zero.mpr (hp ⟨hs, hst⟩)

end Rhone.Statistics.Identifiability.ThreeSampling
