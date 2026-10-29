/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SimultaneousOnsetSeparation
public import Rhone.Statistics.Identifiability.IntegrablePanLaw

/-! # Continuous version of the upper density of a proper integrable pan model -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability
namespace ProperIntegrablePanModel

noncomputable def continuousNonDiagonal (P : ProperIntegrablePanModel) (t : ℝ) : ℝ :=
  P.pre.nonDiagonal (max 0 t)

noncomputable def continuousUpperDensity (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  h p.1 * P.continuousNonDiagonal p.1 * h p.2 *
    Real.exp (integrablePanClock P.rate p.1 - integrablePanClock P.rate p.2)

noncomputable def continuousBranchFlux (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (t : ℝ) : ℝ := h t * P.continuousNonDiagonal t

theorem continuousNonDiagonal_continuous (P : ProperIntegrablePanModel) :
    Continuous P.continuousNonDiagonal :=
  (halfLineAC_continuousOn (fun _T hT => P.pre.nonDiagonal_ac hT)).comp_continuous
    (continuous_const.max continuous_id) (fun t => show max 0 t ∈ Ici (0 : ℝ) from le_max_left 0 t)

theorem continuousNonDiagonal_of_nonneg (P : ProperIntegrablePanModel)
    {t : ℝ} (ht : 0 ≤ t) : P.continuousNonDiagonal t = P.pre.nonDiagonal t := by
  simp only [continuousNonDiagonal, max_eq_right ht]

theorem continuousUpperDensity_continuous (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (hh : Continuous h) : Continuous (P.continuousUpperDensity h) := by
  have hN := P.continuousNonDiagonal_continuous
  have hH := integrablePanClock_continuous P.pre.rate_integrable
  unfold continuousUpperDensity
  fun_prop

theorem continuousBranchFlux_nonneg (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (hn : ∀ t, 0 ≤ t → 0 ≤ h t) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ P.continuousBranchFlux h t :=
  mul_nonneg (hn t ht) (P.pre.nonDiagonal_nonneg (le_max_left _ _))

theorem continuousUpperDensity_nonneg (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (hn : ∀ t, 0 ≤ t → 0 ≤ h t) {p : ℝ × ℝ}
    (hp : p ∈ upperWedge) : 0 ≤ P.continuousUpperDensity h p :=
  mul_nonneg (mul_nonneg (P.continuousBranchFlux_nonneg h hn hp.1.le)
    (hn p.2 (hp.1.trans hp.2).le)) (Real.exp_pos _).le

theorem upperDensity_ae_eq_continuous (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (he : P.rate =ᵐ[volume.restrict (Ioi (0 : ℝ))] h) :
    P.pre.upperDensity =ᵐ[planeVolume.restrict upperWedge] P.continuousUpperDensity h := by
  have he' : ∀ᵐ t, 0 < t → P.rate t = h t := (ae_restrict_iff' measurableSet_Ioi).mp he
  have hf : ∀ᵐ p ∂planeVolume, 0 < p.1 → P.rate p.1 = h p.1 :=
    Measure.quasiMeasurePreserving_fst.ae he'
  have hs : ∀ᵐ p ∂planeVolume, 0 < p.2 → P.rate p.2 = h p.2 :=
    Measure.quasiMeasurePreserving_snd.ae he'
  filter_upwards [hf.filter_mono (ae_mono Measure.restrict_le_self),
    hs.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem upperWedge_open.measurableSet] with p hpf hps hp
  simp only [IntegrablePanPreModel.upperDensity, continuousUpperDensity,
    hpf hp.1, hps (hp.1.trans hp.2), P.continuousNonDiagonal_of_nonneg hp.1.le]

theorem jointLaw_eq_continuous_upper (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (he : P.rate =ᵐ[volume.restrict (Ioi (0 : ℝ))] h) :
    P.pre.jointLaw = regularJointLaw P.pre.diagonalDensity (P.continuousUpperDensity h) := by
  have htri : triangularDensityLaw P.pre.upperDensity =
      triangularDensityLaw (P.continuousUpperDensity h) := by
    apply withDensity_congr_ae
    filter_upwards [P.upperDensity_ae_eq_continuous h he] with p hp
    exact congrArg ENNReal.ofReal hp
  rw [P.pre.jointLaw_eq_regular, regularJointLaw, regularJointLaw, htri]

theorem continuousUpperDensity_self (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (t : ℝ) :
    P.continuousUpperDensity h (t,t) = P.continuousBranchFlux h t * h t := by
  simp [continuousUpperDensity, continuousBranchFlux]

theorem continuousUpperDensity_lintegral (P : ProperIntegrablePanModel)
    (h : ℝ → ℝ) (hn : ∀ t, 0 ≤ t → 0 ≤ h t)
    (he : P.rate =ᵐ[volume.restrict (Ioi (0 : ℝ))] h) {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (P.continuousUpperDensity h (s,t))) =
      ENNReal.ofReal (P.continuousBranchFlux h s) := by
  have he' : P.rate =ᵐ[volume.restrict (Ioi s)] h :=
    he.filter_mono (ae_mono (Measure.restrict_mono (Ioi_subset_Ioi hs) le_rfl))
  calc
    _ = ∫⁻ t in Ioi s, ENNReal.ofReal
        (P.continuousBranchFlux h s * conditionalPairDensity P.rate
          (integrablePanClock P.rate) s t) := by
      apply lintegral_congr_ae
      filter_upwards [he'] with t ht
      congr 1
      simp only [continuousUpperDensity, continuousBranchFlux, conditionalPairDensity, ht]
      ring
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (P.continuousBranchFlux_nonneg h hn hs)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        integrable_conditionalPair_lintegral_one P.pre.rate_integrable P.pre.rate_nonneg
          P.clock_diverges hs, mul_one]

end ProperIntegrablePanModel
end Rhone.Statistics.Identifiability
