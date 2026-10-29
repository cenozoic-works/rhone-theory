/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingLawWitness
public import Rhone.Statistics.Identifiability.TimeVaryingEqualLawSurvival
public import Rhone.Statistics.Identifiability.SimultaneousOnsetWitness

/-! # Full observable-law separation at simultaneous essential mechanism onset -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Rhone.Statistics.Identifiability

theorem timeVaryingJointLaw_eq_pan_determinant_zero (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (P : ProperPanModel) (he : timeVaryingJointLaw k c q r = P.law)
    {t : ℝ} (ht : 0 < t) :
    timeVaryingPairSurvival k c q 0 0 t * timeVaryingUpperDensity k c q r (t,t) -
      timeVaryingPairExitDensity k c q 0 0 t * timeVaryingBranchFlux k c q r 1 2 t = 0 := by
  have hu := timeVaryingJointLaw_eq_pan_upper k c q r hc hq hr hcn hqn hrn P he
  have htrace := upper_density_eq_trace
    (timeVaryingJointDensities_continuous k c q r hc hq hr).2.1
    P.upperDensity_continuous hu ht
  rw [htrace, P.upperDensity_self,
    timeVaryingJointLaw_eq_pan_branchFlux k c q r hc hq hr hcn hqn hrn P he ht
      (hpair t ht.le),
    ← timeVaryingJointLaw_eq_pan_rate_mul_survival k c q r hc hq hr hcn hqn hrn
      hpair P he ht]
  ring

theorem timeVaryingJointLaw_ne_pan_of_positive_witness (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) (hct : 0 < c t)
    (hw : 0 < SimultaneousOnset.witness k c q r t) (P : ProperPanModel) :
    timeVaryingJointLaw k c q r ≠ P.law := by
  intro he
  have hz := timeVaryingJointLaw_eq_pan_determinant_zero k c q r hc hq hr hcn hqn hrn
    hpair P he ht
  rw [timeVarying_observable_determinant k c q r hc hq] at hz
  have hp : 0 < (c t)^2 * SimultaneousOnset.witness k c q r t :=
    mul_pos (sq_pos_of_pos hct) hw
  linarith

theorem timeVaryingJointLaw_ne_pan_of_onset_exposures (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (hQ : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, q u)
    (hR : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, r u)
    (hC : ∀ δ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c t)
    (P : ProperPanModel) : timeVaryingJointLaw k c q r ≠ P.law := by
  obtain ⟨δ, hδ, hw⟩ := SimultaneousOnset.exists_positive_witness_horizon k c q r
    hc hq hr hcn hqn hrn
  obtain ⟨t, ht, htδ, hct⟩ := hC δ hδ
  exact timeVaryingJointLaw_ne_pan_of_positive_witness k c q r hc hq hr hcn hqn hrn hpair
    ht hct (hw t ht htδ (hQ t ht) (hR t ht)) P

def firstEssentialOnsetZero (f : ℝ → ℝ) : Prop :=
  ∀ t, 0 < t → 0 < volume ({u | 0 < f u} ∩ Ioo 0 t)

theorem firstEssentialOnsetZero_iff_exposures (f : ℝ → ℝ)
    (hf : Continuous f) (hn : ∀ t, 0 ≤ t → 0 ≤ f t) :
    firstEssentialOnsetZero f ↔ ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, f u := by
  have hi (t : ℝ) (ht : 0 < t) :
      (0 < ∫ u in (0 : ℝ)..t, f u) ↔ 0 < volume ({u | 0 < f u} ∩ Ioo 0 t) := by
    rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) t)] f := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact hn u hu.1.le
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn
      (hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self)]
    have hs : Function.support f ∩ Ioo 0 t = {u | 0 < f u} ∩ Ioo 0 t := by
      ext u
      simp only [mem_inter_iff, Function.mem_support, mem_ofPred_eq]
      constructor
      · rintro ⟨hfu, hu⟩
        exact ⟨lt_of_le_of_ne (hn u hu.1.le) (Ne.symm hfu), hu⟩
      · rintro ⟨hfu, hu⟩
        exact ⟨hfu.ne', hu⟩
    rw [hs]
  constructor
  · intro h t ht
    exact (hi t ht).mpr (h t ht)
  · intro h t ht
    exact (hi t ht).mp (h t ht)

theorem timeVaryingJointLaw_ne_pan_of_firstEssentialOnsetZero
    (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    (hQ : firstEssentialOnsetZero q) (hR : firstEssentialOnsetZero r)
    (hC : ∀ δ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c t)
    (P : ProperPanModel) : timeVaryingJointLaw k c q r ≠ P.law :=
  timeVaryingJointLaw_ne_pan_of_onset_exposures k c q r hc hq hr hcn hqn hrn hpair
    ((firstEssentialOnsetZero_iff_exposures q hq hqn).mp hQ)
    ((firstEssentialOnsetZero_iff_exposures r hr hrn).mp hR) hC P

end Rhone.Statistics.Identifiability
