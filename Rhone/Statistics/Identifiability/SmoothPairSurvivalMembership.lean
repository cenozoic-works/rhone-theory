/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SmoothPairSurvivalReconstruction
public import Rhone.Statistics.Identifiability.ThreeSamplePanMembership

/-! # An observable smooth weighted survival fixes the unique candidate pan law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership

def weightedSurvival (μ : Measure (ℝ × ℝ)) (t : ℝ) : ℝ :=
  (1/3 : ℝ) * (1 - (μ.map Prod.fst).real (Ioc 0 t)) +
    (2/3 : ℝ) * (1 - (μ.map Prod.snd).real (Ioc 0 t))

lemma weightedSurvival_pan (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (hp : Tendsto (integratedClock rate) atTop atTop)
    {t : ℝ} (ht : 0 ≤ t) :
    weightedSurvival (PanThreeSample.law rate) t = Real.exp (-integratedClock rate t) := by
  unfold weightedSurvival
  rw [PanThreeSample.random_pair_survival rate hr hn hp ht,
    panPairLaw_real_Ioc rate hr hn ht]
  ring

namespace SmoothPairSurvival

def Matches (P : SmoothPairSurvival) (μ : Measure (ℝ × ℝ)) : Prop :=
  ∀ t, 0 ≤ t → weightedSurvival μ t = P.u t

lemma rate_eq_of_survival (P : SmoothPairSurvival) (rate : ℝ → ℝ)
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

theorem pan_representable_iff_eq_candidate (P : SmoothPairSurvival)
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

def candidateDensity (P : SmoothPairSurvival) (p : ℝ × ℝ) : ℝ :=
  3 * P.u p.1 * P.d p.1 * P.d p.2

lemma candidateDensity_continuous (P : SmoothPairSurvival) : Continuous P.candidateDensity := by
  exact ((continuous_const.mul (P.continuous_u.comp continuous_fst)).mul
    (P.continuous_d.comp continuous_fst)).mul (P.continuous_d.comp continuous_snd)

lemma candidateDensity_nonnegative (P : SmoothPairSurvival) {p : ℝ × ℝ}
    (hp : p ∈ upperWedge) : 0 ≤ P.candidateDensity p := by
  have hu := (P.positive p.1 hp.1.le).le
  have h1 := P.decreasing p.1 hp.1.le
  have h2 := P.decreasing p.2 (hp.1.trans hp.2).le
  have h := mul_nonneg_of_nonpos_of_nonpos h1 h2
  unfold candidateDensity
  nlinarith

lemma candidate_law_density (P : SmoothPairSurvival) :
    PanThreeSample.law P.firstProfile.rate = triangularDensityLaw P.candidateDensity := by
  unfold PanThreeSample.law triangularDensityLaw
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  exact congrArg ENNReal.ofReal (P.jointDensity_eq hp.1.le (hp.1.trans hp.2).le)

lemma eq_candidate_iff_density (P : SmoothPairSurvival) (j : ℝ × ℝ → ℝ)
    (hj : Continuous j) (hn : ∀ p ∈ upperWedge, 0 ≤ j p) :
    triangularDensityLaw j = PanThreeSample.law P.firstProfile.rate ↔
      EqOn j P.candidateDensity upperWedge := by
  rw [P.candidate_law_density]
  constructor
  · intro he
    unfold triangularDensityLaw at he
    have ha := (withDensity_eq_iff_of_sigmaFinite hj.measurable.ennreal_ofReal.aemeasurable
      P.candidateDensity_continuous.measurable.ennreal_ofReal.aemeasurable).mp he
    have hreal : j =ᵐ[planeVolume.restrict upperWedge] P.candidateDensity := by
      filter_upwards [ha, ae_restrict_mem upperWedge_open.measurableSet] with p hp hpos
      exact (ENNReal.ofReal_eq_ofReal_iff (hn p hpos) (P.candidateDensity_nonnegative hpos)).mp hp
    exact Measure.eqOn_open_of_ae_eq hreal upperWedge_open hj.continuousOn
      P.candidateDensity_continuous.continuousOn
  · intro he
    unfold triangularDensityLaw
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
    exact congrArg ENNReal.ofReal (he hp)

theorem pan_representable_iff_density (P : SmoothPairSurvival) (j : ℝ × ℝ → ℝ)
    (hj : Continuous j) (hn : ∀ p ∈ upperWedge, 0 ≤ j p)
    (hm : P.Matches (triangularDensityLaw j)) :
    PanRepresentable (triangularDensityLaw j) ↔ EqOn j P.candidateDensity upperWedge := by
  rw [P.pan_representable_iff_eq_candidate _ hm, P.eq_candidate_iff_density j hj hn]

end SmoothPairSurvival
end Rhone.Statistics.Identifiability.ThreeSampleMembership
