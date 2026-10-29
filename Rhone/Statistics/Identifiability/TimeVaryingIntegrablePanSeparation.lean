/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanContinuousUpper
public import Rhone.Statistics.Identifiability.TimeVaryingIntegrablePanHazard

/-! # Time-varying island joint law versus integrable pan models: equalities, separation -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability

theorem timeVaryingJointLaw_eq_integrable_pan_upper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) (P : ProperIntegrablePanModel)
    (he : timeVaryingJointLaw k c q r = P.pre.jointLaw)
    (h : ℝ → ℝ) (hh : Continuous h) (hn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hae : P.rate =ᵐ[volume.restrict (Ioi (0 : ℝ))] h) :
    EqOn (timeVaryingUpperDensity k c q r) (P.continuousUpperDensity h) upperWedge := by
  rw [timeVaryingJointLaw_eq_regular k c q r hc hq hr,
    P.jointLaw_eq_continuous_upper h hae] at he
  exact regularJointLaw_identifies_upper
    (timeVaryingJointDensities_continuous k c q r hc hq hr).2.1
    (P.continuousUpperDensity_continuous h hh)
    (timeVaryingJointDensities_nonneg k c q r hc hq hr hcn hqn hrn).2.1
    (fun _ hp => P.continuousUpperDensity_nonneg h hn hp) he

theorem timeVaryingJointLaw_eq_integrable_pan_branchFlux (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) (P : ProperIntegrablePanModel)
    (he : timeVaryingJointLaw k c q r = P.pre.jointLaw)
    (h : ℝ → ℝ) (hh : Continuous h) (hn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hae : P.rate =ᵐ[volume.restrict (Ioi (0 : ℝ))] h)
    {t : ℝ} (ht : 0 < t)
    (hpair : ∀ i, Tendsto (timeVaryingPairSurvival k c q t i) atTop (𝓝 0)) :
    timeVaryingBranchFlux k c q r 1 2 t = P.continuousBranchFlux h t := by
  have hu := timeVaryingJointLaw_eq_integrable_pan_upper k c q r hc hq hr hcn hqn hrn
    P he h hh hn hae
  have hi : (∫⁻ u in Ioi t, ENNReal.ofReal (timeVaryingUpperDensity k c q r (t,u))) =
      ∫⁻ u in Ioi t, ENNReal.ofReal (P.continuousUpperDensity h (t,u)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro u hu'
    exact congrArg ENNReal.ofReal (hu (show (t,u) ∈ upperWedge from ⟨ht, hu'⟩))
  unfold timeVaryingUpperDensity at hi
  rw [timeVaryingBranchDensity_lintegral k c q r hc hq hr hcn hqn hrn ht.le 1 2 hpair,
    P.continuousUpperDensity_lintegral h hn hae ht.le] at hi
  exact (ENNReal.ofReal_eq_ofReal_iff
    (timeVaryingBranchFlux_nonneg k c q r hc hq hr hcn hqn hrn ht.le 1 2)
    (P.continuousBranchFlux_nonneg h hn ht.le)).mp hi

theorem timeVaryingJointLaw_eq_integrable_pan_determinant_of_repr
    (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) (P : ProperIntegrablePanModel)
    (he : timeVaryingJointLaw k c q r = P.pre.jointLaw)
    (h : ℝ → ℝ) (hh : Continuous h) (hn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hae : P.rate =ᵐ[volume.restrict (Ioi (0 : ℝ))] h)
    {t : ℝ} (ht : 0 < t)
    (hpair : ∀ i, Tendsto (timeVaryingPairSurvival k c q t i) atTop (𝓝 0))
    (hS : h t * timeVaryingPairSurvival k c q 0 0 t =
      timeVaryingPairExitDensity k c q 0 0 t) :
    timeVaryingPairSurvival k c q 0 0 t * timeVaryingUpperDensity k c q r (t,t) -
      timeVaryingPairExitDensity k c q 0 0 t * timeVaryingBranchFlux k c q r 1 2 t = 0 := by
  have hu := timeVaryingJointLaw_eq_integrable_pan_upper k c q r hc hq hr hcn hqn hrn
    P he h hh hn hae
  have htrace := upper_density_eq_trace
    (timeVaryingJointDensities_continuous k c q r hc hq hr).2.1
    (P.continuousUpperDensity_continuous h hh) hu ht
  rw [htrace, P.continuousUpperDensity_self,
    timeVaryingJointLaw_eq_integrable_pan_branchFlux k c q r hc hq hr hcn hqn hrn
      P he h hh hn hae ht hpair, ← hS]
  ring

theorem timeVaryingJointLaw_eq_integrable_pan_determinant_zero
    (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperIntegrablePanModel)
    (he : timeVaryingJointLaw k c q r = P.pre.jointLaw) {t : ℝ} (ht : 0 < t) :
    timeVaryingPairSurvival k c q 0 0 t * timeVaryingUpperDensity k c q r (t,t) -
      timeVaryingPairExitDensity k c q 0 0 t * timeVaryingBranchFlux k c q r 1 2 t = 0 :=
  timeVaryingJointLaw_eq_integrable_pan_determinant_of_repr k c q r hc hq hr hcn hqn hrn
    P he (timeVaryingCanonicalHazard k c q)
    (timeVaryingCanonicalHazard_continuous k c q hc hq hcn hqn)
    (fun t _ => timeVaryingCanonicalHazard_nonneg k c q hc hq hcn hqn t)
    (timeVaryingJointLaw_eq_integrablePan_rate_ae_canonicalHazard k c q r hc hq hr
      hcn hqn hrn hpair P he) ht (hpair t ht.le)
    (timeVaryingCanonicalHazard_mul_survival k c q hc hq hcn hqn ht.le)

theorem timeVaryingJointLaw_ne_integrable_pan_of_positive_witness
    (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) (hct : 0 < c t)
    (hw : 0 < SimultaneousOnset.witness k c q r t) (P : ProperIntegrablePanModel) :
    timeVaryingJointLaw k c q r ≠ P.pre.jointLaw := by
  intro he
  have hz := timeVaryingJointLaw_eq_integrable_pan_determinant_zero k c q r hc hq hr
    hcn hqn hrn hpair P he ht
  rw [timeVarying_observable_determinant k c q r hc hq] at hz
  have hp : 0 < (c t)^2 * SimultaneousOnset.witness k c q r t :=
    mul_pos (sq_pos_of_pos hct) hw
  linarith

theorem timeVaryingJointLaw_ne_integrable_pan_of_onset_exposures
    (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (hQ : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, q u)
    (hR : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, r u)
    (hC : ∀ δ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c t)
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw := by
  obtain ⟨δ, hδ, hw⟩ := SimultaneousOnset.exists_positive_witness_horizon k c q r
    hc hq hr hcn hqn hrn
  obtain ⟨t, ht, htδ, hct⟩ := hC δ hδ
  exact timeVaryingJointLaw_ne_integrable_pan_of_positive_witness k c q r hc hq hr
    hcn hqn hrn hpair ht hct (hw t ht htδ (hQ t ht) (hR t ht)) P

theorem timeVaryingJointLaw_ne_integrable_pan_of_firstEssentialOnsetZero
    (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (hQ : firstEssentialOnsetZero q) (hR : firstEssentialOnsetZero r)
    (hC : ∀ δ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c t)
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw :=
  timeVaryingJointLaw_ne_integrable_pan_of_onset_exposures k c q r hc hq hr hcn hqn hrn hpair
    ((firstEssentialOnsetZero_iff_exposures q hq hqn).mp hQ)
    ((firstEssentialOnsetZero_iff_exposures r hr hrn).mp hR) hC P

end Rhone.Statistics.Identifiability
