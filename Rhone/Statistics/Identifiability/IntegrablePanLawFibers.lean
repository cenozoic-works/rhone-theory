/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanLawIdentification
public import Rhone.Statistics.Identifiability.IntegrablePanGauge
public import Rhone.Statistics.Identifiability.IntegrablePanObservableReconstruction
public import Mathlib.MeasureTheory.Measure.Support

/-! # Exact joint-law fibres for locally integrable panmictic rates -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

noncomputable def integrablePanClockMeasure (rate : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ici 0)).withDensity (fun t => ENNReal.ofReal (rate t))

theorem integrablePanClockMeasure_ae_iff {rate : ℝ → ℝ} {p : ℝ → Prop}
    (hr : LocallyIntegrableOn rate (Ici 0) volume) :
    (∀ᵐ t ∂integrablePanClockMeasure rate, p t) ↔
      ∀ᵐ t, 0 ≤ t → 0 < rate t → p t := by
  rw [integrablePanClockMeasure,
    ae_withDensity_iff' hr.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
    ae_restrict_iff' measurableSet_Ici]
  simp only [ENNReal.ofReal_ne_zero_iff, mem_Ici]

theorem integrablePanClockMeasure_congr {rate rate' : ℝ → ℝ}
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t) :
    integrablePanClockMeasure rate = integrablePanClockMeasure rate' := by
  apply withDensity_congr_ae
  change ∀ᵐ t ∂volume.restrict (Ici 0), ENNReal.ofReal (rate t) = ENNReal.ofReal (rate' t)
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards [hr] with t ht ht0
  rw [ht ht0]

theorem integrablePanClock_congr_ae {rate rate' : ℝ → ℝ}
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t) :
    EqOn (integrablePanClock rate) (integrablePanClock rate') (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rw [integrablePanClock_eq_integral rate ht, integrablePanClock_eq_integral rate' ht]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hr] with s hs hmem
  exact hs ((by simpa only [uIoc_of_le ht] using hmem : s ∈ Ioc 0 t).1.le)

theorem integrable_pan_jointLaw_eq_of_fluxes
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hd : ∀ᵐ t, 0 ≤ t → P.diagonalDensity t = Q.diagonalDensity t)
    (hn : ∀ᵐ t, 0 ≤ t → rate t * P.nonDiagonal t = rate' t * Q.nonDiagonal t) :
    P.jointLaw = Q.jointLaw := by
  rw [P.jointLaw_eq_regular, Q.jointLaw_eq_regular]
  apply regularJointLaw_congr_ae
  · change ∀ᵐ t ∂volume.restrict (Ioi 0), P.diagonalDensity t = Q.diagonalDensity t
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact hd.mono (fun _ ht hp => ht hp.le)
  · have hH := integrablePanClock_congr_ae hr
    have hf : ∀ᵐ p ∂planeVolume,
        0 ≤ p.1 → rate p.1 * P.nonDiagonal p.1 = rate' p.1 * Q.nonDiagonal p.1 :=
      Measure.quasiMeasurePreserving_fst.ae hn
    have hs : ∀ᵐ p ∂planeVolume, 0 ≤ p.2 → rate p.2 = rate' p.2 :=
      Measure.quasiMeasurePreserving_snd.ae hr
    filter_upwards [hf.filter_mono (ae_mono Measure.restrict_le_self),
      hs.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem upperWedge_open.measurableSet] with p hpf hps hp
    have hs0 : 0 ≤ p.2 := (hp.1.trans hp.2).le
    simp only [IntegrablePanPreModel.upperDensity, hpf hp.1.le, hps hs0,
      hH hp.1.le, hH hs0]

theorem integrable_pan_diagonal_flux_determines_law
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hd : ∀ᵐ t, 0 ≤ t → P.diagonalDensity t = Q.diagonalDensity t) :
    P.jointLaw = Q.jointLaw := by
  have hG := (integrable_pan_diagonal_identifies_observables P Q hr hd).1
  apply integrable_pan_jointLaw_eq_of_fluxes P Q hr hd
  filter_upwards [hr, hd] with t hrt hdt ht
  have htot := hG ht
  have hdiag := hdt ht
  change rate t * P.D t = rate' t * Q.D t at hdiag
  dsimp only [IntegrablePanPreModel.total] at htot
  change rate t * (P.R t + P.U t) = rate' t * (Q.R t + Q.U t)
  rw [← hrt ht] at hdiag ⊢
  nlinarith only [hdiag, congrArg (fun x => rate t * x) htot]

theorem integrable_pan_exposure_determines_law
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hx : ∀ᵐ t, 0 ≤ t → 0 < rate t → P.exposure t = Q.exposure t) :
    P.jointLaw = Q.jointLaw := by
  obtain ⟨hd, hn⟩ := integrablePanPreModel_gauge_fluxes_ae P Q hr hx
  exact integrable_pan_jointLaw_eq_of_fluxes P Q hr hd hn

theorem integrable_pan_jointLaw_iff_exposure_ae
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t) :
    P.jointLaw = Q.jointLaw ↔
      P.exposure =ᵐ[integrablePanClockMeasure rate] Q.exposure := by
  simp only [Filter.EventuallyEq]
  rw [integrablePanClockMeasure_ae_iff P.rate_integrable]
  constructor
  · intro h
    have hd := P.diagonal_identifies_flux_ae Q
      (congrArg (fun μ => μ.restrict timeDiagonal) h)
    exact integrable_pan_diagonal_identifies_exposure_ae P Q hr hd
  · exact integrable_pan_exposure_determines_law P Q hr

theorem ProperIntegrablePanModel.jointLaw_iff_marginal_and_diagonal
    (P Q : ProperIntegrablePanModel) :
    P.pre.jointLaw = Q.pre.jointLaw ↔
      P.pre.jointLaw.map Prod.fst = Q.pre.jointLaw.map Prod.fst ∧
      P.pre.jointLaw.restrict timeDiagonal = Q.pre.jointLaw.restrict timeDiagonal := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hm, hd⟩
    exact integrable_pan_diagonal_flux_determines_law P.pre Q.pre
      (P.marginals_identify_clock Q hm).2 (P.pre.diagonal_identifies_flux_ae Q.pre hd)

theorem ProperIntegrablePanModel.jointLaw_iff_rate_and_exposure
    (P Q : ProperIntegrablePanModel) :
    P.pre.jointLaw = Q.pre.jointLaw ↔
      P.rate =ᵐ[volume.restrict (Ici 0)] Q.rate ∧
      P.pre.exposure =ᵐ[integrablePanClockMeasure P.rate] Q.pre.exposure := by
  simp only [Filter.EventuallyEq]
  rw [ae_restrict_iff' measurableSet_Ici,
    integrablePanClockMeasure_ae_iff P.pre.rate_integrable]
  constructor
  · intro h
    obtain ⟨hr, _, hx⟩ := P.equal_law_identifies_rate_and_exposure Q h
    exact ⟨hr, hx⟩
  · rintro ⟨hr, hx⟩
    exact integrable_pan_exposure_determines_law P.pre Q.pre hr hx

theorem continuous_ae_eq_iff_eqOn_measure_support {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    f =ᵐ[μ] g ↔ EqOn f g μ.support := by
  constructor
  · intro h
    exact fun _ hx => μ.support_subset_of_isClosed (isClosed_eq hf hg) h hx
  · intro h
    filter_upwards [μ.support_mem_ae] with t ht
    exact h ht

theorem IntegrablePanPreModel.exposure_continuous
    {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate) : Continuous P.exposure :=
  integrablePanClock_continuous P.recomb_integrable

theorem ProperIntegrablePanModel.jointLaw_iff_rate_and_exposure_on_support
    (P Q : ProperIntegrablePanModel) :
    P.pre.jointLaw = Q.pre.jointLaw ↔
      P.rate =ᵐ[volume.restrict (Ici 0)] Q.rate ∧
      EqOn P.pre.exposure Q.pre.exposure (integrablePanClockMeasure P.rate).support := by
  rw [P.jointLaw_iff_rate_and_exposure Q,
    continuous_ae_eq_iff_eqOn_measure_support P.pre.exposure_continuous Q.pre.exposure_continuous]

end Rhone.Statistics.Identifiability
