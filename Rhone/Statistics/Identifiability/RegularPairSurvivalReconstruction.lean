/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RegularFirstSurvivalProfile
public import Rhone.Statistics.Identifiability.IntegratedNormPower

/-! # Locally absolutely continuous weighted survival constructs its proper pan candidate -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership

structure RegularPairSurvival where
  u : ℝ → ℝ
  d : ℝ → ℝ
  continuous_u : Continuous u
  locallyIntegrable_d : LocallyIntegrable d volume
  ac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval u 0 T
  derivative_ae : ∀ᵐ t, 0 ≤ t → HasDerivAt u (d t) t
  initial : u 0 = 1
  positive : ∀ t, 0 ≤ t → 0 < u t
  decreasing_ae : ∀ᵐ t, 0 ≤ t → d t ≤ 0
  proper : Tendsto u atTop (𝓝 0)

namespace RegularPairSurvival

def firstProfile (P : RegularPairSurvival) : FirstSurvivalProfile where
  survival := fun t => P.u t ^ 3
  density := fun t => -3 * P.u t ^ 2 * P.d t
  continuous_survival := P.continuous_u.pow 3
  initial := by simp [P.initial]
  positive := fun t ht => pow_pos (P.positive t ht) 3
  ac := fun T hT => IntegratedNormPower.absolutelyContinuousOnInterval_pow (P.ac T hT) 3
  density_locallyIntegrable :=
    (P.locallyIntegrable_d.continuous_mul (continuous_const.mul (P.continuous_u.pow 2)))
      |>.locallyIntegrableOn _
  density_nonnegative := by
    filter_upwards [P.decreasing_ae] with t ht ht0
    have hd := ht ht0
    have hu := sq_nonneg (P.u t)
    nlinarith
  derivative_ae := by
    filter_upwards [P.derivative_ae] with t ht ht0
    convert! (ht ht0).pow 3 using 1
    ring
  proper := by simpa using P.proper.pow 3

lemma rate_eq_ae (P : RegularPairSurvival) :
    ∀ᵐ t, 0 ≤ t → P.firstProfile.rate t = -P.d t / P.u t := by
  filter_upwards [P.firstProfile.rate_eq_ae] with t ht ht0
  rw [ht ht0]
  change -3 * P.u t ^ 2 * P.d t / (3 * P.u t ^ 3) = -P.d t / P.u t
  field_simp [(P.positive t ht0).ne']

lemma survival_eq_clock (P : RegularPairSurvival) {t : ℝ} (ht : 0 ≤ t) :
    P.u t = Real.exp (-integratedClock P.firstProfile.rate t) := by
  apply (show Odd 3 by decide).pow_injective
  have he := P.firstProfile.survival_eq_clock ht
  change P.u t ^ 3 = Real.exp (-3 * integratedClock P.firstProfile.rate t) at he
  dsimp only
  rw [← Real.exp_nat_mul]
  convert! he using 1
  ring_nf

def candidateDensity (P : RegularPairSurvival) (p : ℝ × ℝ) : ℝ :=
  3 * P.u p.1 * P.d p.1 * P.d p.2

lemma jointDensity_eq_at (P : RegularPairSurvival) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hrs : P.firstProfile.rate s = -P.d s / P.u s)
    (hrt : P.firstProfile.rate t = -P.d t / P.u t) :
    PanThreeSample.jointDensity P.firstProfile.rate (s,t) = P.candidateDensity (s,t) := by
  rw [PanThreeSample.jointDensity_exp, hrs, hrt]
  have he : Real.exp (-2 * integratedClock P.firstProfile.rate s -
      integratedClock P.firstProfile.rate t) = P.u s ^ 2 * P.u t := by
    rw [P.survival_eq_clock hs, P.survival_eq_clock ht, ← Real.exp_nat_mul,
      ← Real.exp_add]
    congr 1
    ring_nf
  rw [he]
  unfold candidateDensity
  field_simp [(P.positive s hs).ne', (P.positive t ht).ne']

lemma jointDensity_eq_ae (P : RegularPairSurvival) :
    PanThreeSample.jointDensity P.firstProfile.rate =ᵐ[planeVolume.restrict upperWedge]
      P.candidateDensity := by
  have hf : ∀ᵐ p ∂planeVolume, 0 ≤ p.1 →
      P.firstProfile.rate p.1 = -P.d p.1 / P.u p.1 :=
    Measure.quasiMeasurePreserving_fst.ae P.rate_eq_ae
  have hs : ∀ᵐ p ∂planeVolume, 0 ≤ p.2 →
      P.firstProfile.rate p.2 = -P.d p.2 / P.u p.2 :=
    Measure.quasiMeasurePreserving_snd.ae P.rate_eq_ae
  filter_upwards [hf.filter_mono (ae_mono Measure.restrict_le_self),
    hs.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem upperWedge_open.measurableSet] with p hp1 hp2 hp
  exact P.jointDensity_eq_at hp.1.le (hp.1.trans hp.2).le
    (hp1 hp.1.le) (hp2 (hp.1.trans hp.2).le)

lemma candidate_law_density (P : RegularPairSurvival) :
    PanThreeSample.law P.firstProfile.rate = triangularDensityLaw P.candidateDensity := by
  unfold PanThreeSample.law triangularDensityLaw
  apply withDensity_congr_ae
  exact P.jointDensity_eq_ae.fun_comp ENNReal.ofReal

end RegularPairSurvival
end Rhone.Statistics.Identifiability.ThreeSampleMembership
