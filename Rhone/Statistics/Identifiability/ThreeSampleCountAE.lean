/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleCountSeparation
public import Rhone.Statistics.Identifiability.IntegrablePanLawFibers

/-! # Null-set and negative-time changes do not alter the three-sample count law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace PanThreeSample

def nonnegativeRepresentative (rate : ℝ → ℝ) (t : ℝ) : ℝ :=
  (panZeroExtension rate t + |panZeroExtension rate t|) / 2

theorem representative_nonneg (rate : ℝ → ℝ) (t : ℝ) :
    0 ≤ nonnegativeRepresentative rate t := by
  unfold nonnegativeRepresentative
  have h := neg_abs_le (panZeroExtension rate t)
  linarith

theorem representative_locallyIntegrable {rate : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume) :
    LocallyIntegrable (nonnegativeRepresentative rate) volume := by
  have hz := panZeroExtension_locallyIntegrable hr
  have hzNorm : LocallyIntegrable (fun t => ‖panZeroExtension rate t‖) volume :=
    fun t => (hz t).norm
  have hh := (hz.add hzNorm).smul (1 / 2 : ℝ)
  convert hh using 1
  ext t
  simp only [nonnegativeRepresentative, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Real.norm_eq_abs]
  ring

theorem representative_eq_ae {rate : ℝ → ℝ}
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) :
    ∀ᵐ t, 0 ≤ t → rate t = nonnegativeRepresentative rate t := by
  filter_upwards [hn] with t ht ht0
  simp only [nonnegativeRepresentative, panZeroExtension_of_nonneg rate ht0,
    abs_of_nonneg (ht ht0)]
  ring

theorem integratedClock_eq_of_halfLine_ae {rate rate' : ℝ → ℝ}
    (he : ∀ᵐ t, 0 ≤ t → rate t = rate' t) {t : ℝ} (ht : 0 ≤ t) :
    integratedClock rate t = integratedClock rate' t := by
  rw [clock_eq_halfLine rate ht, clock_eq_halfLine rate' ht]
  exact integrablePanClock_congr_ae he ht

theorem law_congr_halfLine_ae {rate rate' : ℝ → ℝ}
    (he : ∀ᵐ t, 0 ≤ t → rate t = rate' t) : law rate = law rate' := by
  unfold law triangularDensityLaw
  apply withDensity_congr_ae
  have hf : ∀ᵐ p ∂planeVolume, 0 ≤ p.1 → rate p.1 = rate' p.1 :=
    Measure.quasiMeasurePreserving_fst.ae he
  have hs : ∀ᵐ p ∂planeVolume, 0 ≤ p.2 → rate p.2 = rate' p.2 :=
    Measure.quasiMeasurePreserving_snd.ae he
  filter_upwards [hf.filter_mono (ae_mono Measure.restrict_le_self),
    hs.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem upperWedge_open.measurableSet] with p hpf hps hp
  rw [jointDensity_exp, jointDensity_exp, hpf hp.1.le,
    hps (hp.1.trans hp.2).le, integratedClock_eq_of_halfLine_ae he hp.1.le,
    integratedClock_eq_of_halfLine_ae he (hp.1.trans hp.2).le]

theorem countLaw_congr_halfLine_ae (mutationRate : ℝ) {rate rate' : ℝ → ℝ}
    (he : ∀ᵐ t, 0 ≤ t → rate t = rate' t) :
    countLaw mutationRate rate = countLaw mutationRate rate' := by
  simp only [countLaw, durationLaw, law_congr_halfLine_ae he]

theorem representative_clock_diverges {rate : ℝ → ℝ}
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    Tendsto (integratedClock (nonnegativeRepresentative rate)) atTop atTop := by
  apply htail.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [clock_eq_halfLine _ ht]
  exact integrablePanClock_congr_ae (representative_eq_ae hn) ht

theorem countLaw_probability_halfLine (mutationRate : ℝ) (hmutation : 0 ≤ mutationRate)
    (rate : ℝ → ℝ) (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    IsProbabilityMeasure (countLaw mutationRate rate) := by
  rw [countLaw_congr_halfLine_ae mutationRate (representative_eq_ae hn)]
  exact countLaw_probability mutationRate (nonnegativeRepresentative rate) hmutation
    (representative_locallyIntegrable hr) (representative_nonneg rate)
    (representative_clock_diverges hn htail)

end PanThreeSample

theorem island_three_countLaw_ne_pan_countLaw_halfLine (k : ℕ) {c q mutationRate : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < mutationRate)
    (rate : ℝ → ℝ) (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    IslandThreeTimes.countLaw k c q mutationRate ≠
      PanThreeSample.countLaw mutationRate rate := by
  have hne := island_three_countLaw_ne_pan_countLaw k hc hq hmutation
    (PanThreeSample.nonnegativeRepresentative rate)
    (PanThreeSample.representative_locallyIntegrable hr)
    (PanThreeSample.representative_nonneg rate)
    (PanThreeSample.representative_clock_diverges hn htail)
  intro he
  apply hne
  exact he.trans (PanThreeSample.countLaw_congr_halfLine_ae mutationRate
    (PanThreeSample.representative_eq_ae hn))

theorem island_three_counts_ne_proper_integrable_pan (k : ℕ) {c q mutationRate : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hmutation : 0 < mutationRate)
    (P : ProperIntegrablePanModel) :
    IslandThreeTimes.countLaw k c q mutationRate ≠
      PanThreeSample.countLaw mutationRate P.rate :=
  island_three_countLaw_ne_pan_countLaw_halfLine k hc hq hmutation P.rate
    P.pre.rate_integrable P.pre.rate_nonneg P.clock_diverges

end Rhone.Statistics.Identifiability
