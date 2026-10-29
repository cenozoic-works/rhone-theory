/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanLaw

/-! # Nonnegative-integral decomposition of the AC/AE pan joint-law Laplace transform -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

theorem density_lintegral_upperWedge_ae (f : ℝ × ℝ → ℝ≥0∞)
    (hf : AEMeasurable f (planeVolume.restrict upperWedge)) :
    (∫⁻ p in upperWedge, f p ∂planeVolume) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi s, f (s, t) := by
  rw [← lintegral_indicator upperWedge_open.measurableSet]
  change (∫⁻ p, upperWedge.indicator f p ∂(volume : Measure ℝ).prod volume) = _
  rw [lintegral_prod _ ((aemeasurable_indicator_iff upperWedge_open.measurableSet).mpr hf),
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs),
      ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : s < t <;> simp [upperWedge, hs, ht]
  · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
    have hz : (fun t => upperWedge.indicator f (s, t)) = fun _ => 0 := by
      funext t
      simp [upperWedge, hs]
    rw [hz, lintegral_zero]

theorem regularJointLaw_lintegral_symmetric (δ : ℝ → ℝ) (j w : ℝ × ℝ → ℝ)
    (hδ : AEMeasurable δ (volume.restrict (Ioi 0)))
    (hj : AEMeasurable j (planeVolume.restrict upperWedge))
    (hw : Measurable w) (hwn : ∀ p, 0 ≤ w p) (hws : ∀ p, w p.swap = w p) :
    (∫⁻ p, ENNReal.ofReal (w p) ∂regularJointLaw δ j) =
      (∫⁻ s in Ioi 0, ENNReal.ofReal (w (s, s) * δ s)) +
      (∫⁻ s in Ioi 0, ∫⁻ t in Ioi s, ENNReal.ofReal (w (s, t) * j (s, t))) +
      (∫⁻ s in Ioi 0, ∫⁻ t in Ioi s, ENNReal.ofReal (w (s, t) * j (s, t))) := by
  have hd : (∫⁻ p, ENNReal.ofReal (w p) ∂diagonalDensityLaw δ) =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (w (s, s) * δ s) := by
    rw [diagonalDensityLaw, lintegral_map (g := fun t : ℝ => (t, t)) hw.ennreal_ofReal
      (measurable_id.prodMk measurable_id),
      lintegral_withDensity_eq_lintegral_mul₀ (g := fun t => ENNReal.ofReal (w (t, t)))
        hδ.ennreal_ofReal
        (hw.ennreal_ofReal.comp (measurable_id.prodMk measurable_id)).aemeasurable]
    apply lintegral_congr
    intro s
    change ENNReal.ofReal (δ s) * ENNReal.ofReal (w (s, s)) = _
    rw [ENNReal.ofReal_mul (hwn (s, s)), mul_comm]
  have ht : (∫⁻ p, ENNReal.ofReal (w p) ∂triangularDensityLaw j) =
      ∫⁻ s in Ioi 0, ∫⁻ t in Ioi s, ENNReal.ofReal (w (s, t) * j (s, t)) := by
    rw [triangularDensityLaw,
      lintegral_withDensity_eq_lintegral_mul₀ hj.ennreal_ofReal hw.ennreal_ofReal.aemeasurable]
    have he : (fun p => (ENNReal.ofReal (j p) * ENNReal.ofReal (w p))) =
        fun p => ENNReal.ofReal (w p * j p) := by
      funext p
      rw [ENNReal.ofReal_mul (hwn p), mul_comm]
    change (∫⁻ p in upperWedge, ENNReal.ofReal (j p) * ENNReal.ofReal (w p) ∂planeVolume) = _
    rw [he]
    exact density_lintegral_upperWedge_ae _ ((hw.aemeasurable.mul hj).ennreal_ofReal)
  rw [regularJointLaw, lintegral_add_measure, lintegral_add_measure,
    lintegral_map (g := Prod.swap) hw.ennreal_ofReal (measurable_snd.prodMk measurable_fst)]
  simp_rw [hws]
  rw [hd, ht]

namespace IntegrablePanPreModel
variable {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate)

theorem jointLaw_laplace_lintegral (k : ℝ) (v : ℝ → ℝ)
    (hv : AEMeasurable v (volume.restrict (Ioi 0)))
    (hvn : ∀ᵐ s ∂volume.restrict (Ioi 0), 0 ≤ v s)
    (hkernel : ∀ᵐ s ∂volume.restrict (Ioi 0),
      (∫⁻ t in Ioi s, ENNReal.ofReal (rate t *
        Real.exp (integrablePanClock rate s - integrablePanClock rate t - k * (t - s)))) =
        ENNReal.ofReal (v s)) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (-k * (p.1 + p.2))) ∂P.jointLaw) =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (Real.exp (-2 * k * s) *
        (P.diagonalDensity s + 2 * (rate s * P.nonDiagonal s * v s))) := by
  let w : ℝ × ℝ → ℝ := fun p => Real.exp (-k * (p.1 + p.2))
  let A : ℝ → ℝ := fun s => Real.exp (-2 * k * s) * P.diagonalDensity s
  let B : ℝ → ℝ := fun s => Real.exp (-2 * k * s) * (rate s * P.nonDiagonal s * v s)
  have hw : Measurable w := Real.measurable_exp.comp
    ((measurable_fst.add measurable_snd).const_mul (-k))
  have hw0 : ∀ s, w (s, s) = Real.exp (-2 * k * s) := by
    intro s
    dsimp [w]
    congr 1
    ring
  have he : ∀ s t, w (s, t) * P.upperDensity (s, t) =
      (Real.exp (-2 * k * s) * (rate s * P.nonDiagonal s)) *
        (rate t * Real.exp (integrablePanClock rate s - integrablePanClock rate t - k * (t - s)))
          := by
    intro s t
    dsimp [w, upperDensity]
    have hexp : Real.exp (-k * (s+t)) *
        Real.exp (integrablePanClock rate s - integrablePanClock rate t) =
      Real.exp (-2*k*s) *
        Real.exp (integrablePanClock rate s - integrablePanClock rate t - k*(t-s)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    linear_combination (rate s * P.nonDiagonal s * rate t) * hexp
  have ht : (∫⁻ s in Ioi 0, ∫⁻ t in Ioi s, ENNReal.ofReal (w (s,t) * P.upperDensity (s,t))) =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (B s) := by
    apply lintegral_congr_ae
    filter_upwards [hkernel, P.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioi] with s hs hsr hmem
    have hc : 0 ≤ Real.exp (-2*k*s) * (rate s * P.nonDiagonal s) :=
      mul_nonneg (Real.exp_pos _).le (mul_nonneg (hsr hmem.le) (P.nonDiagonal_nonneg hmem.le))
    simp_rw [he, ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hs, ← ENNReal.ofReal_mul hc]
    congr 1
    dsimp [B]
    ring
  have hmA : AEMeasurable A (volume.restrict (Ioi 0)) :=
    (Real.measurable_exp.comp (measurable_id.const_mul (-2*k))).aemeasurable.mul
      P.diagonalDensity_aemeasurable
  have hmB : AEMeasurable B (volume.restrict (Ioi 0)) :=
    (Real.measurable_exp.comp (measurable_id.const_mul (-2*k))).aemeasurable.mul
      (P.nonDiagonalFlux_aemeasurable.mul hv)
  have hnA : ∀ᵐ s ∂volume.restrict (Ioi 0), 0 ≤ A s := by
    filter_upwards [P.diagonalDensity_nonneg_ae] with s hs
    exact mul_nonneg (Real.exp_pos _).le hs
  have hnB : ∀ᵐ s ∂volume.restrict (Ioi 0), 0 ≤ B s := by
    filter_upwards [P.nonDiagonalFlux_nonneg_ae, hvn] with s hs hsv
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hs hsv)
  rw [P.jointLaw_eq_regular, regularJointLaw_lintegral_symmetric _ _ w
    P.diagonalDensity_aemeasurable P.upperDensity_aemeasurable hw
    (fun p => (Real.exp_pos _).le) (fun p => by simp [w, add_comm])]
  simp_rw [hw0]
  rw [ht]
  change (∫⁻ s in Ioi 0, ENNReal.ofReal (A s)) +
    (∫⁻ s in Ioi 0, ENNReal.ofReal (B s)) + (∫⁻ s in Ioi 0, ENNReal.ofReal (B s)) = _
  rw [← lintegral_add_left' (f := fun s => ENNReal.ofReal (A s)) hmA.ennreal_ofReal,
    ← lintegral_add_left' (f := fun s => ENNReal.ofReal (A s) + ENNReal.ofReal (B s))
      (hmA.ennreal_ofReal.add hmB.ennreal_ofReal)]
  apply lintegral_congr_ae
  filter_upwards [hnA, hnB] with s hsA hsB
  rw [← ENNReal.ofReal_add hsA hsB, ← ENNReal.ofReal_add (add_nonneg hsA hsB) hsB]
  congr 1
  dsimp [A, B]
  ring

theorem jointLaw_laplace_integral (k : ℝ) (v : ℝ → ℝ)
    (hv : AEMeasurable v (volume.restrict (Ioi 0)))
    (hvn : ∀ᵐ s ∂volume.restrict (Ioi 0), 0 ≤ v s)
    (hkernel : ∀ᵐ s ∂volume.restrict (Ioi 0),
      (∫⁻ t in Ioi s, ENNReal.ofReal (rate t *
        Real.exp (integrablePanClock rate s - integrablePanClock rate t - k * (t - s)))) =
        ENNReal.ofReal (v s)) :
    (∫ p, Real.exp (-k * (p.1 + p.2)) ∂P.jointLaw) =
      ∫ s in Ioi 0, Real.exp (-2 * k * s) *
        (P.diagonalDensity s + 2 * (rate s * P.nonDiagonal s * v s)) := by
  have hw : Measurable (fun p : ℝ × ℝ => Real.exp (-k * (p.1 + p.2))) :=
    Real.measurable_exp.comp ((measurable_fst.add measurable_snd).const_mul (-k))
  have hm : AEMeasurable (fun s => Real.exp (-2 * k * s) *
      (P.diagonalDensity s + 2 * (rate s * P.nonDiagonal s * v s)))
        (volume.restrict (Ioi 0)) :=
    (Real.measurable_exp.comp (measurable_id.const_mul (-2*k))).aemeasurable.mul
      (P.diagonalDensity_aemeasurable.add ((P.nonDiagonalFlux_aemeasurable.mul hv).const_mul 2))
  have hn : ∀ᵐ s ∂volume.restrict (Ioi 0), 0 ≤ Real.exp (-2 * k * s) *
      (P.diagonalDensity s + 2 * (rate s * P.nonDiagonal s * v s)) := by
    filter_upwards [P.diagonalDensity_nonneg_ae, P.nonDiagonalFlux_nonneg_ae, hvn]
      with s hδ ha hv0
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg hδ
      (mul_nonneg (by norm_num) (mul_nonneg ha hv0)))
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun p => (Real.exp_pos _).le))
    hw.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable,
    P.jointLaw_laplace_lintegral k v hv hvn hkernel]

end IntegrablePanPreModel
end Rhone.Statistics.Identifiability
