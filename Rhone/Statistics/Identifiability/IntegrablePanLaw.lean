/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AEDensityMarginals

/-! # Joint laws for the AC/AE pan model -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

namespace IntegrablePanPreModel
variable {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate)

def nonDiagonal (t : ℝ) : ℝ := P.R t + P.U t

def diagonalDensity (t : ℝ) : ℝ := rate t * P.D t

noncomputable def upperDensity (p : ℝ × ℝ) : ℝ :=
  rate p.1 * P.nonDiagonal p.1 * rate p.2 *
    Real.exp (integrablePanClock rate p.1 - integrablePanClock rate p.2)

noncomputable def jointLaw : Measure (ℝ × ℝ) :=
  clockJointLaw rate (integrablePanClock rate) P.D P.nonDiagonal

theorem jointLaw_eq_regular : P.jointLaw = regularJointLaw P.diagonalDensity P.upperDensity := rfl

theorem nonDiagonal_ac {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval P.nonDiagonal 0 T :=
  (P.R_ac T hT).fun_add (P.U_ac T hT)

theorem nonDiagonal_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ P.nonDiagonal t :=
  add_nonneg (P.R_nonneg t ht) (P.U_nonneg t ht)

theorem diagonalDensity_aemeasurable :
    AEMeasurable P.diagonalDensity (volume.restrict (Ioi 0)) := by
  have hd : AEMeasurable P.D (volume.restrict (Ici 0)) :=
    ((halfLineAC_continuousOn P.D_ac).aestronglyMeasurable measurableSet_Ici).aemeasurable
  exact (P.rate_integrable.aestronglyMeasurable.aemeasurable.mul hd).mono_measure
    (Measure.restrict_mono Ioi_subset_Ici_self le_rfl)

theorem nonDiagonalFlux_aemeasurable :
    AEMeasurable (fun t => rate t * P.nonDiagonal t) (volume.restrict (Ioi 0)) := by
  have hn : AEMeasurable P.nonDiagonal (volume.restrict (Ici 0)) :=
    ((halfLineAC_continuousOn (fun T hT => P.nonDiagonal_ac hT)).aestronglyMeasurable
      measurableSet_Ici).aemeasurable
  exact (P.rate_integrable.aestronglyMeasurable.aemeasurable.mul hn).mono_measure
    (Measure.restrict_mono Ioi_subset_Ici_self le_rfl)

theorem upperDensity_aemeasurable :
    AEMeasurable P.upperDensity (planeVolume.restrict upperWedge) := by
  have hr : AEMeasurable (panZeroExtension rate) volume :=
    (panZeroExtension_locallyIntegrable P.rate_integrable).aestronglyMeasurable.aemeasurable
  have hn : AEMeasurable (panZeroExtension P.nonDiagonal) volume :=
    halfLineAC_zeroExtension_aemeasurable (fun T hT => P.nonDiagonal_ac hT)
  have hH := (integrablePanClock_continuous P.rate_integrable).measurable
  have hprod : AEMeasurable (fun p : ℝ × ℝ =>
      panZeroExtension rate p.1 * panZeroExtension P.nonDiagonal p.1 *
      panZeroExtension rate p.2 *
      Real.exp (integrablePanClock rate p.1 - integrablePanClock rate p.2)) planeVolume :=
    ((hr.comp_fst.mul hn.comp_fst).mul hr.comp_snd).mul
      (Real.measurable_exp.comp ((hH.comp measurable_fst).sub
        (hH.comp measurable_snd))).aemeasurable
  apply hprod.restrict.congr
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  simp only [upperDensity, panZeroExtension_of_nonneg rate hp.1.le,
    panZeroExtension_of_nonneg P.nonDiagonal hp.1.le,
    panZeroExtension_of_nonneg rate (hp.1.trans hp.2).le]

theorem diagonalDensity_nonneg_ae :
    ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ P.diagonalDensity t := by
  filter_upwards [P.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with t ht hmem
  exact mul_nonneg (ht hmem.le) (P.D_positive t hmem.le).le

theorem nonDiagonalFlux_nonneg_ae :
    ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ rate t * P.nonDiagonal t := by
  filter_upwards [P.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with t ht hmem
  exact mul_nonneg (ht hmem.le) (P.nonDiagonal_nonneg hmem.le)

theorem upperDensity_nonneg_ae :
    ∀ᵐ p ∂planeVolume.restrict upperWedge, 0 ≤ P.upperDensity p := by
  have hf : ∀ᵐ p ∂planeVolume, 0 ≤ p.1 → 0 ≤ rate p.1 :=
    Measure.quasiMeasurePreserving_fst.ae P.rate_nonneg
  have hs : ∀ᵐ p ∂planeVolume, 0 ≤ p.2 → 0 ≤ rate p.2 :=
    Measure.quasiMeasurePreserving_snd.ae P.rate_nonneg
  filter_upwards [hf.filter_mono (ae_mono Measure.restrict_le_self),
    hs.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem upperWedge_open.measurableSet] with p hpf hps hp
  exact mul_nonneg (mul_nonneg (mul_nonneg (hpf hp.1.le)
    (P.nonDiagonal_nonneg hp.1.le)) (hps (hp.1.trans hp.2).le)) (Real.exp_pos _).le

theorem source_ae_hasDerivAt :
    ∀ᵐ t, 0 ≤ t → HasDerivAt
      (fun s => -(P.total s * Real.exp (integrablePanClock rate s)))
      (rate t * P.nonDiagonal t * Real.exp (integrablePanClock rate t)) t := by
  filter_upwards [P.total_ae_hasDerivAt,
    integrablePanClock_ae_hasDerivAt P.rate_integrable] with t ht hH ht0
  convert! ((ht ht0).mul (hH ht0).exp).neg using 1
  dsimp [total, nonDiagonal]
  ring

theorem source_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => rate s * P.nonDiagonal s *
      Real.exp (integrablePanClock rate s)) volume 0 t := by
  apply ac_intervalIntegrable_ae ((P.total_ac ht).mul
    (ac_exp (integrablePanClock_ac P.rate_integrable 0 t))).neg
  filter_upwards [P.source_ae_hasDerivAt] with s hs hmem
  exact hs ((by simpa only [uIcc_of_le ht] using hmem : s ∈ Icc 0 t).1)

theorem source_integral {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, rate s * P.nonDiagonal s *
      Real.exp (integrablePanClock rate s)) =
        1 - P.total t * Real.exp (integrablePanClock rate t) := by
  have he := ac_integral_eq_sub_ae ((P.total_ac ht).mul
    (ac_exp (integrablePanClock_ac P.rate_integrable 0 t))).neg
    (show ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt
      (fun x => -(P.total x * Real.exp (integrablePanClock rate x)))
      (rate s * P.nonDiagonal s * Real.exp (integrablePanClock rate s)) s from by
        filter_upwards [P.source_ae_hasDerivAt] with s hs hmem
        exact hs ((by simpa only [uIcc_of_le ht] using hmem : s ∈ Icc 0 t).1))
  simpa only [Pi.neg_apply, Pi.mul_apply, integrablePanClock_zero, total_zero, Real.exp_zero,
    mul_one, sub_neg_eq_add, neg_add_eq_sub] using he

theorem marginal_mass_identity {t : ℝ} (ht : 0 ≤ t) :
    P.total t + pendingPairMass rate (integrablePanClock rate) P.nonDiagonal t =
      Real.exp (-integrablePanClock rate t) := by
  rw [pendingPairMass, primitiveFrom, P.source_integral ht]
  have he : Real.exp (-integrablePanClock rate t) *
      Real.exp (integrablePanClock rate t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination -P.total t * he

theorem pendingPairMass_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ pendingPairMass rate (integrablePanClock rate) P.nonDiagonal t := by
  unfold pendingPairMass primitiveFrom
  apply mul_nonneg (Real.exp_pos _).le
  apply intervalIntegral.integral_nonneg_of_ae_restrict ht
  change ∀ᵐ s ∂volume.restrict (Icc 0 t),
    0 ≤ rate s * P.nonDiagonal s * Real.exp (integrablePanClock rate s)
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [P.rate_nonneg] with s hs hmem
  exact mul_nonneg (mul_nonneg (hs hmem.1) (P.nonDiagonal_nonneg hmem.1))
    (Real.exp_pos _).le

theorem upperDensity_column {t : ℝ} (ht : 0 < t) (hr : 0 ≤ rate t) :
    (∫⁻ s in Ioo 0 t, ENNReal.ofReal (P.upperDensity (s, t))) =
      ENNReal.ofReal (rate t * pendingPairMass rate (integrablePanClock rate)
        P.nonDiagonal t) := by
  let H := integrablePanClock rate
  let g := fun s => rate s * P.nonDiagonal s * Real.exp (H s)
  have hi : IntegrableOn g (Ioo 0 t) :=
    (P.source_intervalIntegrable ht.le).1.mono_set Ioo_subset_Ioc_self
  have hc : 0 ≤ rate t * Real.exp (-H t) := mul_nonneg hr (Real.exp_pos _).le
  have hn : ∀ᵐ s ∂volume.restrict (Ioo 0 t), 0 ≤ g s := by
    filter_upwards [P.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioo] with s hs hmem
    exact mul_nonneg (mul_nonneg (hs hmem.1.le) (P.nonDiagonal_nonneg hmem.1.le))
      (Real.exp_pos _).le
  simp_rw [upperDensity, clock_density_separated]
  change (∫⁻ s in Ioo 0 t, ENNReal.ofReal ((rate t * Real.exp (-H t)) * g s)) = _
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change ENNReal.ofReal (rate t * Real.exp (-H t)) *
    (∫⁻ s in Ioo 0 t, ENNReal.ofReal (g s)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← ENNReal.ofReal_mul hc]
  have he : (∫ s in Ioo 0 t, g s) = primitiveFrom g 0 t := by
    rw [primitiveFrom, intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]
  rw [he]
  congr 1
  unfold pendingPairMass
  dsimp [g, H]
  ring

theorem triangular_map_snd :
    (triangularDensityLaw P.upperDensity).map Prod.snd =
      (volume.restrict (Ioi 0)).withDensity (fun t =>
        ENNReal.ofReal (rate t * pendingPairMass rate (integrablePanClock rate)
          P.nonDiagonal t)) := by
  rw [triangular_map_snd_positive_ae _ P.upperDensity_aemeasurable]
  apply withDensity_congr_ae
  filter_upwards [P.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with t ht hmem
  exact P.upperDensity_column hmem (ht hmem.le)

end IntegrablePanPreModel

namespace ProperIntegrablePanModel
variable (P : ProperIntegrablePanModel)

theorem conditionalPairLaw_probability {s : ℝ} (hs : 0 ≤ s) :
    IsProbabilityMeasure (conditionalPairLaw P.rate (integrablePanClock P.rate) s) := by
  constructor
  rw [conditionalPairLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact integrable_conditionalPair_lintegral_one P.pre.rate_integrable P.pre.rate_nonneg
    P.clock_diverges hs

theorem upperDensity_tail :
    ∀ᵐ s ∂volume.restrict (Ioi 0),
      (∫⁻ t in Ioi s, ENNReal.ofReal (P.pre.upperDensity (s, t))) =
        ENNReal.ofReal (P.rate s * P.pre.nonDiagonal s) := by
  filter_upwards [P.pre.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with s hs hmem
  have hn := mul_nonneg (hs hmem.le) (P.pre.nonDiagonal_nonneg hmem.le)
  have he : ∀ t, P.pre.upperDensity (s, t) = (P.rate s * P.pre.nonDiagonal s) *
      conditionalPairDensity P.rate (integrablePanClock P.rate) s t := by
    intro t
    unfold IntegrablePanPreModel.upperDensity conditionalPairDensity
    ring
  simp_rw [he, ENNReal.ofReal_mul hn]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    integrable_conditionalPair_lintegral_one P.pre.rate_integrable P.pre.rate_nonneg
      P.clock_diverges hmem.le, mul_one]

theorem triangular_map_fst :
    (triangularDensityLaw P.pre.upperDensity).map Prod.fst =
      (volume.restrict (Ioi 0)).withDensity (fun t =>
        ENNReal.ofReal (P.rate t * P.pre.nonDiagonal t)) := by
  rw [triangular_map_fst_ae _ P.pre.upperDensity_aemeasurable]
  exact withDensity_congr_ae P.upperDensity_tail

theorem jointLaw_map_fst :
    P.pre.jointLaw.map Prod.fst =
      conditionalPairLaw P.rate (integrablePanClock P.rate) 0 := by
  rw [P.pre.jointLaw_eq_regular, regularJointLaw]
  rw [Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
    diagonalDensityLaw_map_fst,
    Measure.map_map (f := Prod.swap) measurable_fst (measurable_snd.prodMk measurable_fst)]
  change _ + _ + (triangularDensityLaw _).map Prod.snd = _
  rw [P.triangular_map_fst, P.pre.triangular_map_snd]
  rw [← withDensity_add_left_ae P.pre.diagonalDensity_aemeasurable.ennreal_ofReal,
    ← withDensity_add_left_ae (P.pre.diagonalDensity_aemeasurable.ennreal_ofReal.add
      P.pre.nonDiagonalFlux_aemeasurable.ennreal_ofReal)]
  unfold conditionalPairLaw
  apply withDensity_congr_ae
  filter_upwards [P.pre.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with t ht hmem
  have hd := mul_nonneg (ht hmem.le) (P.pre.D_positive t hmem.le).le
  have hn := mul_nonneg (ht hmem.le) (P.pre.nonDiagonal_nonneg hmem.le)
  have hp := mul_nonneg (ht hmem.le) (P.pre.pendingPairMass_nonneg hmem.le)
  simp only [Pi.add_apply, IntegrablePanPreModel.diagonalDensity]
  rw [← ENNReal.ofReal_add hd hn, ← ENNReal.ofReal_add (add_nonneg hd hn) hp]
  congr 1
  unfold conditionalPairDensity
  calc
    _ = P.rate t * (P.pre.total t +
        pendingPairMass P.rate (integrablePanClock P.rate) P.pre.nonDiagonal t) := by
      dsimp [IntegrablePanPreModel.total, IntegrablePanPreModel.nonDiagonal]
      ring
    _ = _ := by rw [P.pre.marginal_mass_identity hmem.le, integrablePanClock_zero, zero_sub]

theorem jointLaw_map_swap : P.pre.jointLaw.map Prod.swap = P.pre.jointLaw := by
  rw [P.pre.jointLaw_eq_regular]
  exact regularJointLaw_map_swap _ _

theorem jointLaw_map_snd :
    P.pre.jointLaw.map Prod.snd =
      conditionalPairLaw P.rate (integrablePanClock P.rate) 0 := by
  calc
    _ = (P.pre.jointLaw.map Prod.swap).map Prod.fst := by
      rw [Measure.map_map (f := Prod.swap) measurable_fst
        (measurable_snd.prodMk measurable_fst)]
      rfl
    _ = _ := by rw [P.jointLaw_map_swap, P.jointLaw_map_fst]

theorem firstFlux_lintegral_one :
    (∫⁻ t in Ioi 0, ENNReal.ofReal
      (P.pre.diagonalDensity t + 2 * (P.rate t * P.pre.nonDiagonal t))) = 1 := by
  have hd : ∀ᵐ t, 0 ≤ t → HasDerivAt P.pre.total
      (-(P.pre.diagonalDensity t + 2 * (P.rate t * P.pre.nonDiagonal t))) t := by
    filter_upwards [P.pre.total_ae_hasDerivAt] with t ht ht0
    convert! ht ht0 using 1
    dsimp [IntegrablePanPreModel.diagonalDensity, IntegrablePanPreModel.nonDiagonal]
    ring
  have hn : ∀ᵐ t, 0 ≤ t →
      0 ≤ P.pre.diagonalDensity t + 2 * (P.rate t * P.pre.nonDiagonal t) := by
    filter_upwards [P.pre.rate_nonneg] with t ht ht0
    exact add_nonneg (mul_nonneg (ht ht0) (P.pre.D_positive t ht0).le)
      (mul_nonneg (by norm_num) (mul_nonneg (ht ht0) (P.pre.nonDiagonal_nonneg ht0)))
  have hm := P.pre.diagonalDensity_aemeasurable.add
    (P.pre.nonDiagonalFlux_aemeasurable.const_mul 2)
  have he := ac_flux_lintegral_Ioi (fun b hb => P.pre.total_ac hb) hd hn hm
    P.total_tendsto_zero
  simpa using he

theorem jointLaw_probability : IsProbabilityMeasure P.pre.jointLaw := by
  rw [P.pre.jointLaw_eq_regular]
  exact regularJointLaw_probability_of_tail_ae _ _ _ P.pre.diagonalDensity_aemeasurable
    P.pre.nonDiagonalFlux_aemeasurable P.pre.upperDensity_aemeasurable
    P.pre.diagonalDensity_nonneg_ae P.pre.nonDiagonalFlux_nonneg_ae P.upperDensity_tail
    P.firstFlux_lintegral_one

end ProperIntegrablePanModel
theorem exists_integrablePanJointLaw (rate recomb : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hρ : LocallyIntegrableOn recomb (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hρn : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    ∃ P : IntegrablePanPreModel rate, P.recomb = recomb ∧
      IsProbabilityMeasure P.jointLaw ∧
      P.jointLaw.map Prod.fst = conditionalPairLaw rate (integrablePanClock rate) 0 ∧
      P.jointLaw.map Prod.snd = conditionalPairLaw rate (integrablePanClock rate) 0 := by
  obtain ⟨P, hP⟩ := exists_integrablePanPreModel rate recomb hr hρ hrn hρn
  let Q : ProperIntegrablePanModel := ⟨rate, P, htail⟩
  exact ⟨P, hP, Q.jointLaw_probability, Q.jointLaw_map_fst, Q.jointLaw_map_snd⟩

end Rhone.Statistics.Identifiability
