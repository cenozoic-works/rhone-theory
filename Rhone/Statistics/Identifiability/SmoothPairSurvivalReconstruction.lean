/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RegularFirstSurvivalProfile
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # A smooth positive proper pair-survival curve constructs a proper pan law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership

structure SmoothPairSurvival where
  u : ℝ → ℝ
  d : ℝ → ℝ
  continuous_d : Continuous d
  derivative : ∀ t, HasDerivAt u (d t) t
  initial : u 0 = 1
  positive : ∀ t, 0 ≤ t → 0 < u t
  decreasing : ∀ t, 0 ≤ t → d t ≤ 0
  proper : Tendsto u atTop (𝓝 0)

namespace SmoothPairSurvival
lemma continuous_u (P : SmoothPairSurvival) : Continuous P.u :=
  continuous_iff_continuousAt.mpr fun t => (P.derivative t).continuousAt

lemma contDiff_u (P : SmoothPairSurvival) : ContDiff ℝ 1 P.u := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (P.derivative t).differentiableAt, ?_⟩
  have he : deriv P.u = P.d := funext fun t => (P.derivative t).deriv
  rw [he]
  exact P.continuous_d

def firstProfile (P : SmoothPairSurvival) : FirstSurvivalProfile where
  survival := fun t => P.u t ^ 3
  density := fun t => -3 * P.u t ^ 2 * P.d t
  continuous_survival := P.continuous_u.pow 3
  initial := by simp [P.initial]
  positive := fun t ht => pow_pos (P.positive t ht) 3
  ac := fun _ _ => (P.contDiff_u.pow 3).contDiffOn.absolutelyContinuousOnInterval
  density_locallyIntegrable :=
    ((continuous_const.mul (P.continuous_u.pow 2)).mul P.continuous_d).locallyIntegrable
      |>.locallyIntegrableOn _
  density_nonnegative := ae_of_all _ fun t ht => by
    have hu := sq_nonneg (P.u t)
    have hd := P.decreasing t ht
    nlinarith
  derivative_ae := ae_of_all _ fun t _ => by
    convert! (P.derivative t).pow 3 using 1; ring_nf
  proper := by simpa using P.proper.pow 3

lemma rate_eq (P : SmoothPairSurvival) {t : ℝ} (ht : 0 ≤ t) :
    P.firstProfile.rate t = -P.d t / P.u t := by
  have hu := P.positive t ht
  have hd := P.decreasing t ht
  have hnum : 0 ≤ -3 * P.u t ^ 2 * P.d t := by
    have h := mul_nonneg (sq_nonneg (P.u t)) (neg_nonneg.mpr hd)
    nlinarith
  have hn : 0 ≤ -3 * P.u t ^ 2 * P.d t / (3 * P.u t ^ 3) :=
    div_nonneg hnum (by positivity)
  simp only [FirstSurvivalProfile.rate, PanThreeSample.nonnegativeRepresentative,
    panZeroExtension_of_nonneg _ ht, FirstSurvivalProfile.rawRate, firstProfile,
    max_eq_left ht, abs_of_nonneg hn]
  field_simp [hu.ne']
  ring_nf

lemma survival_eq_clock (P : SmoothPairSurvival) {t : ℝ} (ht : 0 ≤ t) :
    P.u t = Real.exp (-integratedClock P.firstProfile.rate t) := by
  apply (show Odd 3 by decide).pow_injective
  have he := P.firstProfile.survival_eq_clock ht
  change P.u t ^ 3 = Real.exp (-3 * integratedClock P.firstProfile.rate t) at he
  dsimp only
  rw [← Real.exp_nat_mul]
  convert! he using 1; ring_nf

lemma jointDensity_eq (P : SmoothPairSurvival) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    PanThreeSample.jointDensity P.firstProfile.rate (s,t) =
      3 * P.u s * P.d s * P.d t := by
  rw [PanThreeSample.jointDensity_exp, P.rate_eq hs, P.rate_eq ht]
  have he : Real.exp (-2 * integratedClock P.firstProfile.rate s -
      integratedClock P.firstProfile.rate t) = P.u s ^ 2 * P.u t := by
    rw [P.survival_eq_clock hs, P.survival_eq_clock ht, ← Real.exp_nat_mul,
      ← Real.exp_add]
    congr 1
    ring_nf
  rw [he]
  field_simp [(P.positive s hs).ne', (P.positive t ht).ne']

end SmoothPairSurvival
end Rhone.Statistics.Identifiability.ThreeSampleMembership
