/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingJointLaw
public import Rhone.Statistics.Identifiability.ThreeSampleCountAE

/-! # Equal first-merger marginals recover a continuous representative of any L1 pan rate -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

def canonicalRate (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  firstDensity k c q (max t 0) / (3 * survival k c q (max t 0))

lemma canonicalRate_of_nonnegative (k : ℕ) (c q : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    canonicalRate k c q t = firstDensity k c q t / (3 * survival k c q t) := by
  simp only [canonicalRate, max_eq_left ht]

lemma canonicalRate_continuous (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) : Continuous (canonicalRate k c q) := by
  have hm : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  exact ((firstDensity_continuous k c q hc hq).comp hm).div
    (continuous_const.mul ((survival_continuous k c q hc hq).comp hm))
    (fun t => mul_ne_zero (by norm_num)
      (survival_positive k c q hc hq hqn (le_max_right t 0)).ne')

lemma canonicalRate_nonnegative (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) (t : ℝ) :
    0 ≤ canonicalRate k c q t :=
  div_nonneg (firstDensity_nonnegative k c q hc hq hcn hqn (le_max_right t 0))
    (mul_nonneg (by norm_num) (survival_positive k c q hc hq hqn (le_max_right t 0)).le)

lemma canonicalRate_mul_survival (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) :
    3 * canonicalRate k c q t * survival k c q t = firstDensity k c q t := by
  rw [canonicalRate_of_nonnegative k c q ht]
  have hs := (survival_positive k c q hc hq hqn ht).ne'
  field_simp

theorem equal_law_survival (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law k c q = PanThreeSample.law rate) {t : ℝ} (ht : 0 ≤ t) :
    survival k c q t = Real.exp (-(3 * integratedClock rate t)) := by
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) he
  rw [law_first_marginal k c q hc hq hcn hqn hpair,
    PanThreeSample.first_marginal rate hr hn htail] at hm
  have h3 : LocallyIntegrable (fun u => 3 * rate u) volume := by
    convert! hr.smul (3 : ℝ) using 1
  have hCDF := congrArg (fun μ : Measure ℝ => μ.real (Ioc 0 t)) hm
  rw [firstLaw_real_Ioc k c q hc hq hcn hqn ht,
    panPairLaw_real_Ioc _ h3 (fun u => mul_nonneg (by norm_num) (hn u)) ht,
    integratedClock_scale] at hCDF
  linarith

theorem equal_law_rate_ae (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop)
    (he : law k c q = PanThreeSample.law rate) :
    ∀ᵐ t, 0 ≤ t → rate t = canonicalRate k c q t := by
  have hclock : ∀ᵐ t, HasDerivAt (integratedClock rate) (rate t) t := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hr] with t ht
    exact ht 0
  filter_upwards [hclock, volume.ae_ne (0 : ℝ)] with t hH htne ht0
  have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htne)
  have hs (u : ℝ) (hu : 0 ≤ u) := equal_law_survival k c q hc hq hcn hqn hpair
    rate hr hn htail he hu
  have hEq : survival k c q =ᶠ[𝓝 t]
      (fun u => Real.exp (-(3 * integratedClock rate u))) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact hs u hu.le
  have hd : HasDerivAt (fun u => Real.exp (-(3 * integratedClock rate u)))
      (-(3 * rate t) * Real.exp (-(3 * integratedClock rate t))) t := by
    convert! (hH.const_mul (3 : ℝ)).neg.exp using 1
    simp only [Pi.neg_apply]
    ring
  have hederiv := (survival_derivative k c q hc hq t).unique (hd.congr_of_eventuallyEq hEq)
  rw [← hs t ht0] at hederiv
  rw [canonicalRate_of_nonnegative k c q ht0]
  apply (eq_div_iff (mul_ne_zero (by norm_num) (survival_positive k c q hc hq hqn ht0).ne')).mpr
  nlinarith

end Rhone.Statistics.Identifiability.ThreeTimeVarying
