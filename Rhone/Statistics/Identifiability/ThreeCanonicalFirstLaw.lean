/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleCDFStatistic

/-! # The source first-merger marginal always determines a proper continuous pan candidate -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

lemma log_survival_canonical_clock (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.log (survival k c q t) = -3 * integratedClock (canonicalRate k c q) t := by
  have hL := canonicalRate_continuous k c q hc hq hqn
  have hd (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt (fun v => Real.log (survival k c q v)) (-3 * canonicalRate k c q u) u := by
    apply ((survival_derivative k c q hc hq u).log
      (survival_positive k c q hc hq hqn hu).ne').congr_deriv
    rw [canonicalRate_of_nonnegative k c q hu]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u (by rw [uIcc_of_le ht] at hu; exact hu.1))
    ((continuous_const.mul hL).intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul, survival_initial k c q hc hq, Real.log_one,
    sub_zero] at hFTC
  exact hFTC.symm

lemma survival_canonical_clock (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) :
    survival k c q t = Real.exp (-3 * integratedClock (canonicalRate k c q) t) := by
  rw [← log_survival_canonical_clock k c q hc hq hqn ht,
    Real.exp_log (survival_positive k c q hc hq hqn ht)]

lemma canonical_clock_diverges (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    Tendsto (integratedClock (canonicalRate k c q)) atTop atTop := by
  have hs : Tendsto (survival k c q) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨survival_tendsto_zero_of_pair k c q hc hq hcn hqn hproper, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact survival_positive k c q hc hq hqn ht
  have hlog := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hs)
  have hscale := hlog.const_mul_atTop (show (0 : ℝ) < 1 / 3 by norm_num)
  apply hscale.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change (1 / 3 : ℝ) * -Real.log (survival k c q t) = _
  rw [log_survival_canonical_clock k c q hc hq hqn ht]
  ring

end Rhone.Statistics.Identifiability.ThreeTimeVarying
