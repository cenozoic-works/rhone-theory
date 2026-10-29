/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SimultaneousOnsetSeparation
public import Rhone.Statistics.Identifiability.IntegrablePanLaw

/-! # Equal-law survival and continuous hazard representatives for the AC/AE pan class -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

theorem integrable_conditionalPairLaw_tail {rate : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ x, 0 ≤ x → 0 ≤ rate x)
    (htail : Tendsto (integrablePanClock rate) atTop atTop)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    conditionalPairLaw rate (integrablePanClock rate) s (Ioi t) =
      ENNReal.ofReal (Real.exp (integrablePanClock rate s - integrablePanClock rate t)) := by
  let H := integrablePanClock rate
  let F := fun x => Real.exp (H s - H x)
  let g := conditionalPairDensity rate H s
  have hac (b : ℝ) (_hb : t ≤ b) : AbsolutelyContinuousOnInterval F t b :=
    ac_exp (((LipschitzWith.const (H s)).lipschitzOnWith.absolutelyContinuousOnInterval).sub
      (integrablePanClock_ac hr t b))
  have hd : ∀ᵐ x, t ≤ x → HasDerivAt F (-g x) x := by
    filter_upwards [integrablePanClock_ae_hasDerivAt hr] with x hx htx
    convert ((hx ((hs.trans hst).trans htx)).const_sub (H s)).exp using 1
    dsimp [g, conditionalPairDensity]
    ring
  have hn : ∀ᵐ x, t ≤ x → 0 ≤ g x := by
    filter_upwards [hrn] with x hx htx
    exact mul_nonneg (hx ((hs.trans hst).trans htx)) (Real.exp_pos _).le
  have hm : AEMeasurable g (volume.restrict (Ioi t)) :=
    ((hr.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono (fun x hx => (hs.trans hst).trans hx.le) le_rfl))).mul
      ((Real.continuous_exp.comp (continuous_const.sub
        (integrablePanClock_continuous hr))).measurable.aemeasurable)
  have hlim : Tendsto F atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [sub_eq_add_neg, H, Function.comp_apply] using
      tendsto_atBot_add_const_left atTop (H s)
        (tendsto_neg_atTop_atBot.comp htail)
  have he := ac_flux_lintegral_Ioi hac hd hn hm hlim
  rw [conditionalPairLaw, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hst)]
  simpa only [sub_zero] using he

theorem timeVaryingJointLaw_eq_integrablePan_pairExitLaw (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperIntegrablePanModel)
    (he : timeVaryingJointLaw k c q r = P.pre.jointLaw) :
    timeVaryingPairExitLaw k c q 0 0 =
      conditionalPairLaw P.rate (integrablePanClock P.rate) 0 := by
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) he
  rw [timeVaryingJointLaw_map_fst k c q r hc hq hr hcn hqn hrn hpair,
    P.jointLaw_map_fst] at hm
  exact hm

theorem timeVaryingJointLaw_eq_integrablePan_survival (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperIntegrablePanModel)
    (he : timeVaryingJointLaw k c q r = P.pre.jointLaw)
    {t : ℝ} (ht : 0 ≤ t) :
    timeVaryingPairSurvival k c q 0 0 t = Real.exp (-integrablePanClock P.rate t) := by
  have hm := timeVaryingJointLaw_eq_integrablePan_pairExitLaw k c q r hc hq hr hcn hqn hrn
    hpair P he
  have htail := congrArg (fun μ : Measure ℝ => μ (Ioi t)) hm
  rw [timeVaryingPairExitLaw_tail k c q hc hq hcn hqn (le_refl 0) ht 0
      (hpair 0 (le_refl 0) 0),
    integrable_conditionalPairLaw_tail P.pre.rate_integrable P.pre.rate_nonneg
      P.clock_diverges (le_refl 0) ht, integrablePanClock_zero, zero_sub] at htail
  exact (ENNReal.ofReal_eq_ofReal_iff
    (timeVaryingPairSurvival_pos k c q hc hq hcn hqn (le_refl 0) ht 0).le
    (Real.exp_pos _).le).mp htail

theorem timeVaryingJointLaw_eq_integrablePan_rate_mul_survival_ae
    (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperIntegrablePanModel)
    (he : timeVaryingJointLaw k c q r = P.pre.jointLaw) :
    ∀ᵐ t ∂volume.restrict (Ioi 0),
      P.rate t * timeVaryingPairSurvival k c q 0 0 t =
        timeVaryingPairExitDensity k c q 0 0 t := by
  filter_upwards [(integrablePanClock_ae_hasDerivAt P.pre.rate_integrable).filter_mono
    (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioi] with t ht ht0
  have heq : timeVaryingPairSurvival k c q 0 0 =ᶠ[𝓝 t]
      (fun u => Real.exp (-integrablePanClock P.rate u)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht0] with u hu
    exact timeVaryingJointLaw_eq_integrablePan_survival k c q r hc hq hr hcn hqn hrn
      hpair P he hu.le
  have hd := ((ht ht0.le).neg).exp
  have hd' := hd.congr_of_eventuallyEq heq
  have huniq := hd'.unique (timeVaryingPairSurvival_hasDerivAt k c q hc hq 0 t 0)
  simp only [Pi.neg_apply] at huniq
  rw [timeVaryingJointLaw_eq_integrablePan_survival k c q r hc hq hr hcn hqn hrn
    hpair P he ht0.le]
  nlinarith

noncomputable def timeVaryingCanonicalHazard (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  timeVaryingPairExitDensity k c q 0 0 (max 0 t) /
    timeVaryingPairSurvival k c q 0 0 (max 0 t)

@[simp] theorem timeVaryingCanonicalHazard_of_nonneg (k : ℕ) (c q : ℝ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    timeVaryingCanonicalHazard k c q t =
      timeVaryingPairExitDensity k c q 0 0 t / timeVaryingPairSurvival k c q 0 0 t := by
  simp only [timeVaryingCanonicalHazard, max_eq_right ht]

theorem timeVaryingCanonicalHazard_mul_survival (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) :
    timeVaryingCanonicalHazard k c q t * timeVaryingPairSurvival k c q 0 0 t =
      timeVaryingPairExitDensity k c q 0 0 t := by
  rw [timeVaryingCanonicalHazard_of_nonneg k c q ht]
  exact div_mul_cancel₀ _
    (timeVaryingPairSurvival_pos k c q hc hq hcn hqn (le_refl 0) ht 0).ne'

theorem timeVaryingCanonicalHazard_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) :
    Continuous (timeVaryingCanonicalHazard k c q) := by
  have hm : Continuous (fun t : ℝ => max 0 t) := continuous_const.max continuous_id
  have hf : Continuous (timeVaryingPairExitDensity k c q 0 0) :=
    (timeVaryingPairExitDensity_continuous k c q hc hq 0).comp
      (continuous_const.prodMk continuous_id)
  have hS : Continuous (timeVaryingPairSurvival k c q 0 0) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (timeVaryingPairSurvival_hasDerivAt k c q hc hq 0 t 0).continuousAt
  exact (hf.comp hm).div (hS.comp hm) (fun t =>
    (timeVaryingPairSurvival_pos k c q hc hq hcn hqn (le_refl 0) (le_max_left 0 t) 0).ne')

theorem timeVaryingCanonicalHazard_nonneg (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) (t : ℝ) :
    0 ≤ timeVaryingCanonicalHazard k c q t :=
  div_nonneg
    (timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn
      (le_refl 0) (le_max_left 0 t) 0)
    (timeVaryingPairSurvival_pos k c q hc hq hcn hqn
      (le_refl 0) (le_max_left 0 t) 0).le

theorem timeVaryingJointLaw_eq_integrablePan_rate_ae_canonicalHazard
    (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperIntegrablePanModel)
    (he : timeVaryingJointLaw k c q r = P.pre.jointLaw) :
    P.rate =ᵐ[volume.restrict (Ioi 0)] timeVaryingCanonicalHazard k c q := by
  filter_upwards [timeVaryingJointLaw_eq_integrablePan_rate_mul_survival_ae
    k c q r hc hq hr hcn hqn hrn hpair P he,
    ae_restrict_mem measurableSet_Ioi] with t ht ht0
  rw [timeVaryingCanonicalHazard_of_nonneg k c q ht0.le]
  exact (eq_div_iff (timeVaryingPairSurvival_pos k c q hc hq hcn hqn
    (le_refl 0) ht0.le 0).ne').mpr ht

end Rhone.Statistics.Identifiability
