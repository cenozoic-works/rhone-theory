/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingJointMarginalMeasure
public import Rhone.Statistics.Identifiability.UnknownClockMembership

/-! # Equal laws force equal survival for time-varying islands and proper pan models -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem conditionalPairLaw_tail_of_proper_clock (rate H : ℝ → ℝ)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (htail : Tendsto H atTop atTop)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    conditionalPairLaw rate H s (Ioi t) = ENNReal.ofReal (Real.exp (H s-H t)) := by
  have hi := (conditionalPair_integrable rate H hs hrn hd htail).mono_set
    (Ioi_subset_Ioi hst)
  have he : (∫ u in Ioi t, conditionalPairDensity rate H s u) =
      Real.exp (H s-H t) := by
    have h := integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun u hu => conditionalPair_CDF_derivative rate H s u
        (hd u ((hs.trans hst).trans hu)))
      (fun u hu => mul_nonneg (hrn u ((hs.trans hst).trans hu.le))
        (Real.exp_pos (H s-H u)).le)
      ((conditionalPair_survival_tendsto_zero H s htail).const_sub 1)
    convert h using 1
    ring
  rw [conditionalPairLaw, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hst), ← ofReal_integral_eq_lintegral_ofReal hi, he]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (hrn u ((hs.trans hst).trans hu.le)) (Real.exp_pos _).le

theorem timeVaryingJointLaw_eq_pan_pairExitLaw (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperPanModel) (he : timeVaryingJointLaw k c q r = P.law) :
    timeVaryingPairExitLaw k c q 0 0 = conditionalPairLaw P.rate P.clock 0 := by
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) he
  rw [timeVaryingJointLaw_map_fst k c q r hc hq hr hcn hqn hrn hpair,
    P.law_map_fst] at hm
  exact hm

theorem timeVaryingJointLaw_eq_pan_survival (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperPanModel) (he : timeVaryingJointLaw k c q r = P.law)
    {t : ℝ} (ht : 0 ≤ t) :
    timeVaryingPairSurvival k c q 0 0 t = Real.exp (P.clock 0-P.clock t) := by
  have hm := timeVaryingJointLaw_eq_pan_pairExitLaw k c q r hc hq hr hcn hqn hrn
    hpair P he
  have htail := congrArg (fun μ : Measure ℝ => μ (Ioi t)) hm
  rw [timeVaryingPairExitLaw_tail k c q hc hq hcn hqn (le_refl 0) ht 0
      (hpair 0 (le_refl 0) 0),
    conditionalPairLaw_tail_of_proper_clock P.rate P.clock P.rate_nonneg
      P.clock_derivative P.clock_diverges (le_refl 0) ht] at htail
  exact (ENNReal.ofReal_eq_ofReal_iff
    (timeVaryingPairSurvival_pos k c q hc hq hcn hqn (le_refl 0) ht 0).le
    (Real.exp_pos _).le).mp htail

theorem timeVaryingJointLaw_eq_pan_rate_mul_survival (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperPanModel) (he : timeVaryingJointLaw k c q r = P.law)
    {t : ℝ} (ht : 0 < t) :
    P.rate t * timeVaryingPairSurvival k c q 0 0 t =
      timeVaryingPairExitDensity k c q 0 0 t := by
  have heq : timeVaryingPairSurvival k c q 0 0 =ᶠ[𝓝 t]
      (fun u => Real.exp (P.clock 0-P.clock u)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    exact timeVaryingJointLaw_eq_pan_survival k c q r hc hq hr hcn hqn hrn
      hpair P he hu.le
  have hd := ((P.clock_derivative t ht.le).const_sub (P.clock 0)).exp
  have hd' := hd.congr_of_eventuallyEq heq
  have huniq := hd'.unique (timeVaryingPairSurvival_hasDerivAt k c q hc hq 0 t 0)
  rw [timeVaryingJointLaw_eq_pan_survival k c q r hc hq hr hcn hqn hrn hpair P he ht.le]
  nlinarith

end Rhone.Statistics.Identifiability
