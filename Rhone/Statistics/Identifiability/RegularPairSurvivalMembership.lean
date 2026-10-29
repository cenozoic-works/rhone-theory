/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RegularPairSurvivalReconstruction
public import Rhone.Statistics.Identifiability.SmoothPairSurvivalMembership

/-! # AE density membership from an observable locally absolutely continuous survival curve -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership

namespace RegularPairSurvival

def Matches (P : RegularPairSurvival) (μ : Measure (ℝ × ℝ)) : Prop :=
  ∀ t, 0 ≤ t → weightedSurvival μ t = P.u t

lemma rate_eq_of_survival (P : RegularPairSurvival) (rate : ℝ → ℝ)
    (hr : LocallyIntegrable rate volume)
    (he : ∀ t, 0 ≤ t → P.u t = Real.exp (-integratedClock rate t)) :
    ∀ᵐ t, 0 ≤ t → rate t = P.firstProfile.rate t := by
  have hc : ∀ t, 0 ≤ t → integratedClock rate t =
      integratedClock P.firstProfile.rate t := by
    intro t ht
    have h := Real.exp_injective ((he t ht).symm.trans (P.survival_eq_clock ht))
    linarith
  apply ae_nonneg_iff_ae_pos.mpr
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hr,
    LocallyIntegrable.ae_hasDerivAt_integral P.firstProfile.rate_locallyIntegrable]
    with t ht hpt ht0
  have heq : integratedClock rate =ᶠ[𝓝 t] integratedClock P.firstProfile.rate := by
    filter_upwards [eventually_gt_nhds ht0] with s hs
    exact hc s hs.le
  exact (ht 0).unique ((hpt 0).congr_of_eventuallyEq heq)

theorem pan_representable_iff_eq_candidate (P : RegularPairSurvival)
    (μ : Measure (ℝ × ℝ)) (hm : P.Matches μ) :
    PanRepresentable μ ↔ μ = PanThreeSample.law P.firstProfile.rate := by
  constructor
  · rintro ⟨rate, hr, hn, hp, he⟩
    let r := PanThreeSample.nonnegativeRepresentative rate
    have hr' := PanThreeSample.representative_locallyIntegrable hr
    have hn' := PanThreeSample.representative_nonneg rate
    have hp' := PanThreeSample.representative_clock_diverges hn hp
    have he' : μ = PanThreeSample.law r :=
      he.trans (PanThreeSample.law_congr_halfLine_ae (PanThreeSample.representative_eq_ae hn))
    have hs : ∀ t, 0 ≤ t → P.u t = Real.exp (-integratedClock r t) := by
      intro t ht
      rw [← hm t ht, he']
      exact weightedSurvival_pan r hr' hn' hp' ht
    exact he'.trans (PanThreeSample.law_congr_halfLine_ae (P.rate_eq_of_survival r hr' hs))
  · intro he
    exact ⟨P.firstProfile.rate, P.firstProfile.rate_locallyIntegrable.locallyIntegrableOn _,
      ae_of_all _ (fun t _ => P.firstProfile.rate_nonnegative t),
      candidate_proper_halfLine P.firstProfile, he⟩

lemma candidateDensity_aemeasurable (P : RegularPairSurvival) :
    AEMeasurable P.candidateDensity (planeVolume.restrict upperWedge) :=
  (PanThreeSample.density_aemeasurable P.firstProfile.rate
    P.firstProfile.rate_locallyIntegrable).congr P.jointDensity_eq_ae

lemma candidateDensity_nonnegative_ae (P : RegularPairSurvival) :
    ∀ᵐ p ∂planeVolume.restrict upperWedge, 0 ≤ P.candidateDensity p := by
  filter_upwards [P.jointDensity_eq_ae] with p hp
  rw [← hp, PanThreeSample.jointDensity_exp]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (P.firstProfile.rate_nonnegative p.1)) (P.firstProfile.rate_nonnegative p.2))
    (Real.exp_pos _).le

lemma eq_candidate_iff_density_ae (P : RegularPairSurvival) (j : ℝ × ℝ → ℝ)
    (hj : AEMeasurable j (planeVolume.restrict upperWedge))
    (hn : ∀ᵐ p ∂planeVolume.restrict upperWedge, 0 ≤ j p) :
    triangularDensityLaw j = PanThreeSample.law P.firstProfile.rate ↔
      j =ᵐ[planeVolume.restrict upperWedge] P.candidateDensity := by
  rw [P.candidate_law_density]
  constructor
  · intro he
    unfold triangularDensityLaw at he
    have ha := (withDensity_eq_iff_of_sigmaFinite hj.ennreal_ofReal
      P.candidateDensity_aemeasurable.ennreal_ofReal).mp he
    filter_upwards [ha, hn, P.candidateDensity_nonnegative_ae] with p hp hpn hcn
    exact (ENNReal.ofReal_eq_ofReal_iff hpn hcn).mp hp
  · intro he
    unfold triangularDensityLaw
    exact withDensity_congr_ae (he.fun_comp ENNReal.ofReal)

theorem pan_representable_iff_density_ae (P : RegularPairSurvival) (j : ℝ × ℝ → ℝ)
    (hj : AEMeasurable j (planeVolume.restrict upperWedge))
    (hn : ∀ᵐ p ∂planeVolume.restrict upperWedge, 0 ≤ j p)
    (hm : P.Matches (triangularDensityLaw j)) :
    PanRepresentable (triangularDensityLaw j) ↔
      j =ᵐ[planeVolume.restrict upperWedge] P.candidateDensity := by
  rw [P.pan_representable_iff_eq_candidate _ hm, P.eq_candidate_iff_density_ae j hj hn]

end RegularPairSurvival
end Rhone.Statistics.Identifiability.ThreeSampleMembership
