/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockVolterra
public import Rhone.Statistics.Identifiability.CommonClockSumLaw
public import Rhone.Statistics.Identifiability.IntegrablePanLawFibers

/-! # Joint law of the pan model in common-clock form: continuity, nonnegativity, total integral -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace IntegrablePanPreModel
variable {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate)

noncomputable def commonClockD (t : ℝ) : ℝ := P.D (max 0 t)
noncomputable def commonClockN (t : ℝ) : ℝ := P.nonDiagonal (max 0 t)
noncomputable def commonClockDiagonal (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  h t * P.commonClockD t
noncomputable def commonClockFirstFactor (h H : ℝ → ℝ) (t : ℝ) : ℝ :=
  h t * P.commonClockN t * Real.exp (H t)

theorem commonClockD_continuous : Continuous P.commonClockD :=
  (halfLineAC_continuousOn P.D_ac).comp_continuous
    (continuous_const.max continuous_id) (fun t => le_max_left 0 t)
theorem commonClockN_continuous : Continuous P.commonClockN :=
  (halfLineAC_continuousOn (fun _ hT => P.nonDiagonal_ac hT)).comp_continuous
    (continuous_const.max continuous_id) (fun t => le_max_left 0 t)
theorem commonClockDiagonal_continuous {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (P.commonClockDiagonal h) := hh.mul P.commonClockD_continuous
theorem commonClockFirstFactor_continuous {h H : ℝ → ℝ}
    (hh : Continuous h) (hH : Continuous H) : Continuous (P.commonClockFirstFactor h H) :=
  (hh.mul P.commonClockN_continuous).mul (Real.continuous_exp.comp hH)

theorem commonClockDiagonal_nonneg {h : ℝ → ℝ}
    (hn : ∀ t, 0 ≤ t → 0 ≤ h t) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ P.commonClockDiagonal h t :=
  mul_nonneg (hn t ht) (P.D_positive _ (le_max_left _ _)).le
theorem commonClockFirstFactor_nonneg {h H : ℝ → ℝ}
    (hn : ∀ t, 0 ≤ t → 0 ≤ h t) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ P.commonClockFirstFactor h H t :=
  mul_nonneg (mul_nonneg (hn t ht) (P.nonDiagonal_nonneg (le_max_left _ _)))
    (Real.exp_pos _).le

theorem jointLaw_eq_commonClock_regular {h H : ℝ → ℝ}
    (hr : ∀ᵐ t, 0 ≤ t → rate t = h t)
    (hH : EqOn (integrablePanClock rate) H (Ici 0)) :
    P.jointLaw = regularJointLaw (P.commonClockDiagonal h)
      (fun p => P.commonClockFirstFactor h H p.1 * (h p.2 * Real.exp (-H p.2))) := by
  rw [P.jointLaw_eq_regular]
  apply regularJointLaw_congr_ae
  · filter_upwards [hr.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioi] with t ht hmem
    change 0 < t at hmem
    simp only [diagonalDensity, commonClockDiagonal, commonClockD,
      max_eq_right hmem.le, ht hmem.le]
  · have hf : ∀ᵐ p ∂planeVolume, 0 ≤ p.1 → rate p.1 = h p.1 :=
      Measure.quasiMeasurePreserving_fst.ae hr
    have hs : ∀ᵐ p ∂planeVolume, 0 ≤ p.2 → rate p.2 = h p.2 :=
      Measure.quasiMeasurePreserving_snd.ae hr
    filter_upwards [hf.filter_mono (ae_mono Measure.restrict_le_self),
      hs.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem upperWedge_open.measurableSet] with p hpf hps hp
    have hp₂ : 0 ≤ p.2 := (hp.1.trans hp.2).le
    simp only [upperDensity, commonClockFirstFactor, commonClockN,
      max_eq_right hp.1.le, hpf hp.1.le, hps hp₂, hH hp.1.le, hH hp₂]
    rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    ring

theorem commonClock_total_integral {h : ℝ → ℝ}
    (hr : ∀ᵐ t, 0 ≤ t → rate t = h t) {t : ℝ} (ht : 0 ≤ t) :
    P.total t = 1 + ∫ s in (0 : ℝ)..t,
      P.commonClockDiagonal h s - 2 * h s * P.total s := by
  have hd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt P.total
      (P.commonClockDiagonal h s - 2 * h s * P.total s) s := by
    filter_upwards [P.total_ae_hasDerivAt, hr] with s hs hrs hmem
    have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le ht] using hmem : s ∈ Icc 0 t).1
    convert hs hs0 using 1
    simp only [commonClockDiagonal, commonClockD, max_eq_right hs0, hrs hs0, total]
    ring
  have hi := ac_integral_eq_sub_ae (P.total_ac ht) hd
  rw [P.total_zero] at hi
  linarith

theorem commonClockFirstFactor_eq {h H : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    P.commonClockFirstFactor h H t =
      (h t * P.total t - P.commonClockDiagonal h t) / Real.exp (-H t) := by
  simp only [commonClockFirstFactor, commonClockN, commonClockDiagonal, commonClockD,
    max_eq_right ht, total, nonDiagonal, Real.exp_neg, div_inv_eq_mul]
  ring

theorem jointLaw_map_sum_commonClock {h H : ℝ → ℝ}
    (hh : Continuous h) (hHc : Continuous H) (hn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hr : ∀ᵐ t, 0 ≤ t → rate t = h t)
    (hH : EqOn (integrablePanClock rate) H (Ici 0)) :
    P.jointLaw.map (fun p => p.1 + p.2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun z =>
        ENNReal.ofReal (panSumDensity (P.commonClockDiagonal h)
          (P.commonClockFirstFactor h H) (fun t => h t * Real.exp (-H t)) z)) := by
  rw [P.jointLaw_eq_commonClock_regular hr hH]
  exact regularJointLaw_map_sum_pan (P.commonClockDiagonal h)
    (P.commonClockFirstFactor h H) (fun t => h t * Real.exp (-H t))
    (P.commonClockDiagonal_continuous hh).measurable
    (P.commonClockFirstFactor_continuous hh hHc)
    (hh.mul (Real.continuous_exp.comp hHc.neg))
    (fun t ht => P.commonClockDiagonal_nonneg hn ht.le)
    (fun t ht => P.commonClockFirstFactor_nonneg hn ht.le)
    (fun t ht => mul_nonneg (hn t ht.le) (Real.exp_pos _).le)

end IntegrablePanPreModel

theorem integrable_pan_sum_law_identifies_jointLaw
    {rate rate' h : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hh : Continuous h) (hn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hrP : ∀ᵐ t, 0 ≤ t → rate t = h t)
    (hrQ : ∀ᵐ t, 0 ≤ t → rate' t = h t)
    (hsum : P.jointLaw.map (fun p => p.1 + p.2) =
      Q.jointLaw.map (fun p => p.1 + p.2)) : P.jointLaw = Q.jointLaw := by
  let H := integrablePanClock rate
  let f := fun t => h t * Real.exp (-H t)
  let S := fun t => Real.exp (-H t)
  let dP := P.commonClockDiagonal h
  let dQ := Q.commonClockDiagonal h
  let aP := P.commonClockFirstFactor h H
  let aQ := Q.commonClockFirstFactor h H
  have hH : Continuous H := integrablePanClock_continuous P.rate_integrable
  have hfc : Continuous f := hh.mul (Real.continuous_exp.comp hH.neg)
  have hSc : Continuous S := Real.continuous_exp.comp hH.neg
  have hdPc : Continuous dP := P.commonClockDiagonal_continuous hh
  have hdQc : Continuous dQ := Q.commonClockDiagonal_continuous hh
  have haPc : Continuous aP := P.commonClockFirstFactor_continuous hh hH
  have haQc : Continuous aQ := Q.commonClockFirstFactor_continuous hh hH
  have hrates : ∀ᵐ t, 0 ≤ t → rate t = rate' t := by
    filter_upwards [hrP, hrQ] with t hp hq ht
    exact (hp ht).trans (hq ht).symm
  have hclock : EqOn (integrablePanClock rate') H (Ici 0) :=
    (integrablePanClock_congr_ae hrates).symm
  have hlP : P.jointLaw = regularJointLaw dP (fun p => aP p.1 * f p.2) :=
    P.jointLaw_eq_commonClock_regular hrP (fun _ _ => rfl)
  have hlQ : Q.jointLaw = regularJointLaw dQ (fun p => aQ p.1 * f p.2) :=
    Q.jointLaw_eq_commonClock_regular hrQ hclock
  have hfn : ∀ t ≥ 0, 0 ≤ f t := fun t ht => mul_nonneg (hn t ht) (Real.exp_pos _).le
  have he := sum_law_identifies_panSumDensity hdPc.continuousOn haPc.continuousOn hfc.continuousOn
    hdQc.continuousOn haQc.continuousOn hfc.continuousOn
    (fun _ ht => P.commonClockDiagonal_nonneg hn ht)
    (fun _ ht => P.commonClockFirstFactor_nonneg hn ht) hfn
    (fun _ ht => Q.commonClockDiagonal_nonneg hn ht)
    (fun _ ht => Q.commonClockFirstFactor_nonneg hn ht) hfn
    (by rwa [← hlP, ← hlQ])
  let g := fun t => panSumDensity dP aP f (2 * t)
  have hsP : ∀ t ∈ Ici 0, g t = dP t / 2 + 2 *
      ∫ s in (0 : ℝ)..t, ((h s * P.total s - dP s) / S s) * f (2 * t - s) := by
    intro t ht
    change 0 ≤ t at ht
    rw [show g t = panSumDensity dP aP f (2 * t) from rfl, panSumDensity_double]
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le ht] using hs : s ∈ Icc 0 t).1
    dsimp only
    rw [show aP s = (h s * P.total s - dP s) / S s from P.commonClockFirstFactor_eq hs0]
  have hsQ : ∀ t ∈ Ici 0, g t = dQ t / 2 + 2 *
      ∫ s in (0 : ℝ)..t, ((h s * Q.total s - dQ s) / S s) * f (2 * t - s) := by
    intro t ht
    change 0 ≤ t at ht
    rw [show g t = panSumDensity dP aP f (2 * t) from rfl,
      he (show 2 * t ∈ Ici 0 from mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht), panSumDensity_double]
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le ht] using hs : s ∈ Icc 0 t).1
    dsimp only
    rw [show aQ s = (h s * Q.total s - dQ s) / S s from Q.commonClockFirstFactor_eq hs0]
  have hd := (commonClock_reconstruction_unique hfc.continuousOn hh.continuousOn
    hSc.continuousOn (fun _ _ => Real.exp_pos _) hdPc.continuousOn hdQc.continuousOn
    (halfLineAC_continuousOn (fun _ ht => P.total_ac ht))
    (halfLineAC_continuousOn (fun _ ht => Q.total_ac ht))
    (fun _ ht => P.commonClock_total_integral hrP ht)
    (fun _ ht => Q.commonClock_total_integral hrQ ht) hsP hsQ).1
  apply integrable_pan_diagonal_flux_determines_law P Q hrates
  filter_upwards [hrP, hrQ] with t hp hq ht
  have heq := hd ht
  simp only [dP, dQ, IntegrablePanPreModel.commonClockDiagonal,
    IntegrablePanPreModel.commonClockD, max_eq_right ht] at heq
  simpa only [IntegrablePanPreModel.diagonalDensity, hp ht, hq ht] using heq

theorem ProperIntegrablePanModel.marginal_sum_identifies_jointLaw
    (P Q : ProperIntegrablePanModel) (h : ℝ → ℝ)
    (hh : Continuous h) (hn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (hr : ∀ᵐ t, 0 ≤ t → P.rate t = h t)
    (hm : P.pre.jointLaw.map Prod.fst = Q.pre.jointLaw.map Prod.fst)
    (hs : P.pre.jointLaw.map (fun p => p.1 + p.2) =
      Q.pre.jointLaw.map (fun p => p.1 + p.2)) : P.pre.jointLaw = Q.pre.jointLaw := by
  have hrates := (P.marginals_identify_clock Q hm).2
  apply integrable_pan_sum_law_identifies_jointLaw P.pre Q.pre hh hn hr _ hs
  filter_upwards [hr, hrates] with t ht he ht0
  exact (he ht0).symm.trans (ht ht0)

theorem integrable_pan_positive_jointLaw_identifies_recombination
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hpos : ∀ᵐ t, 0 < t → 0 < rate t)
    (he : P.jointLaw = Q.jointLaw) :
    ∀ᵐ t, 0 ≤ t → P.recomb t = Q.recomb t := by
  have hd := P.diagonal_identifies_flux_ae Q
    (congrArg (fun μ : Measure (ℝ × ℝ) => μ.restrict timeDiagonal) he)
  have hx := integrable_pan_diagonal_identifies_exposure_ae P Q hr hd
  have hx' : P.exposure =ᵐ[volume.restrict (Ioi 0)] Q.exposure := by
    change ∀ᵐ t ∂volume.restrict (Ioi 0), P.exposure t = Q.exposure t
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hx, hpos] with t ht hp ht0
    exact ht ht0.le (hp ht0)
  have hE : EqOn P.exposure Q.exposure (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hx' isOpen_Ioi
      P.exposure_continuous.continuousOn Q.exposure_continuous.continuousOn
  apply ae_nonneg_iff_ae_pos.mpr
  filter_upwards [integrablePanClock_ae_hasDerivAt P.recomb_integrable,
    integrablePanClock_ae_hasDerivAt Q.recomb_integrable] with t hp hq ht
  have hevent : Q.exposure =ᶠ[𝓝 t] P.exposure := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hE hs).symm
  exact ((hp ht.le).congr_of_eventuallyEq hevent).unique (hq ht.le)

theorem ProperIntegrablePanModel.marginal_sum_identifies_both_rates
    (P Q : ProperIntegrablePanModel) (h : ℝ → ℝ)
    (hh : Continuous h) (hpos : ∀ t, 0 < t → 0 < h t)
    (hr : ∀ᵐ t, 0 ≤ t → P.rate t = h t)
    (hm : P.pre.jointLaw.map Prod.fst = Q.pre.jointLaw.map Prod.fst)
    (hs : P.pre.jointLaw.map (fun p => p.1 + p.2) =
      Q.pre.jointLaw.map (fun p => p.1 + p.2)) :
    (∀ᵐ t, 0 ≤ t → P.rate t = Q.rate t) ∧
      (∀ᵐ t, 0 ≤ t → P.pre.recomb t = Q.pre.recomb t) := by
  have hrate := (P.marginals_identify_clock Q hm).2
  have hlaw := P.marginal_sum_identifies_jointLaw Q h hh
    (rate_nonneg_of_positive_time h hh hpos) hr hm hs
  refine ⟨hrate, integrable_pan_positive_jointLaw_identifies_recombination
    P.pre Q.pre hrate ?_ hlaw⟩
  filter_upwards [hr] with t ht ht0
  rw [ht ht0.le]
  exact hpos t ht0

theorem ProperIntegrablePanModel.continuous_positive_pair_density_representative
    (P : ProperIntegrablePanModel) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ici 0)) (hpos : ∀ t ≥ 0, 0 < f t)
    (hpair : P.pre.jointLaw.map Prod.fst =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (f t))) :
    ∃ h : ℝ → ℝ, Continuous h ∧ (∀ t ≥ 0, 0 < h t) ∧
      (∀ᵐ t, 0 ≤ t → P.rate t = h t) := by
  let S := fun t => Real.exp (-integrablePanClock P.rate t)
  let h := fun t => f (max 0 t) / S t
  have hS : Continuous S := Real.continuous_exp.comp
    (integrablePanClock_continuous P.pre.rate_integrable).neg
  have hSc (t : ℝ) : 0 < S t := Real.exp_pos _
  have hc : Continuous h :=
    (hf.comp_continuous (continuous_const.max continuous_id) (fun t => le_max_left 0 t)).div
      hS (fun t => (hSc t).ne')
  have hn : ∀ t ≥ 0, 0 < h t := by
    intro t ht
    exact div_pos (hpos _ (le_max_left _ _)) (hSc t)
  refine ⟨h, hc, hn, ?_⟩
  have hm : AEMeasurable (fun t => P.rate t * S t) (volume.restrict (Ioi 0)) :=
    (P.pre.rate_integrable.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono Ioi_subset_Ici_self le_rfl)).mul hS.measurable.aemeasurable
  rw [P.jointLaw_map_fst] at hpair
  simp only [conditionalPairLaw, conditionalPairDensity, integrablePanClock_zero,
    zero_sub] at hpair
  have hd := (withDensity_eq_iff_of_sigmaFinite hm.ennreal_ofReal
    ((hf.mono Ioi_subset_Ici_self).aemeasurable measurableSet_Ioi).ennreal_ofReal).mp hpair
  apply ae_nonneg_iff_ae_pos.mpr
  have hd' := (ae_restrict_iff' measurableSet_Ioi).mp hd
  filter_upwards [hd', P.pre.rate_nonneg] with t ht hrt ht0
  have heq : P.rate t * S t = f t :=
    (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (hrt ht0.le) (hSc t).le)
      (hpos t ht0.le).le).mp (ht ht0)
  dsimp only [h]
  rw [max_eq_right ht0.le]
  exact (eq_div_iff (hSc t).ne').mpr heq

theorem ProperIntegrablePanModel.pair_density_sum_identifies
    (P Q : ProperIntegrablePanModel) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ici 0)) (hpos : ∀ t ≥ 0, 0 < f t)
    (hpair : P.pre.jointLaw.map Prod.fst =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (f t)))
    (hm : P.pre.jointLaw.map Prod.fst = Q.pre.jointLaw.map Prod.fst)
    (hs : P.pre.jointLaw.map (fun p => p.1 + p.2) =
      Q.pre.jointLaw.map (fun p => p.1 + p.2)) :
    P.pre.jointLaw = Q.pre.jointLaw ∧
      (∀ᵐ t, 0 ≤ t → P.rate t = Q.rate t) ∧
      (∀ᵐ t, 0 ≤ t → P.pre.recomb t = Q.pre.recomb t) := by
  obtain ⟨h, hh, hn, hr⟩ := P.continuous_positive_pair_density_representative f hf hpos hpair
  exact ⟨P.marginal_sum_identifies_jointLaw Q h hh (fun t ht => (hn t ht).le) hr hm hs,
    P.marginal_sum_identifies_both_rates Q h hh (fun t ht => hn t ht.le) hr hm hs⟩

end Rhone.Statistics.Identifiability
