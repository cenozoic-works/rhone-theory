/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanLaw
public import Rhone.Statistics.Identifiability.TimeVaryingIntegrablePanHazard

/-! # Strict positive dependence at the level of the pre-merger survival path -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

namespace IntegrablePanPreModel
variable {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate)

theorem twiceTiltedTotal_ae_hasDerivAt :
    ∀ᵐ t, 0 ≤ t → HasDerivAt
      (fun s => P.total s * Real.exp (2 * integrablePanClock rate s))
      (rate t * P.D t * Real.exp (2 * integrablePanClock rate t)) t := by
  filter_upwards [P.total_ae_hasDerivAt,
    integrablePanClock_ae_hasDerivAt P.rate_integrable] with t ht hH ht0
  convert! (ht ht0).mul ((hH ht0).const_mul 2).exp using 1
  dsimp [total]
  ring

theorem twiceTiltedTotal_integral {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
      rate s * P.D s * Real.exp (2 * integrablePanClock rate s)) =
      P.total t * Real.exp (2 * integrablePanClock rate t) - 1 := by
  have he := ac_integral_eq_sub_ae ((P.total_ac ht).mul
    (ac_exp ((integrablePanClock_ac P.rate_integrable 0 t).const_mul 2)))
    (show ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt
      (fun x => P.total x * Real.exp (2 * integrablePanClock rate x))
      (rate s * P.D s * Real.exp (2 * integrablePanClock rate s)) s from by
        filter_upwards [P.twiceTiltedTotal_ae_hasDerivAt] with s hs hmem
        exact hs ((by simpa only [uIcc_of_le ht] using hmem : s ∈ Icc 0 t).1))
  simpa only [Pi.mul_apply, integrablePanClock_zero, mul_zero, total_zero,
    Real.exp_zero, one_mul] using he

theorem twiceTiltedTotal_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s =>
      rate s * P.D s * Real.exp (2 * integrablePanClock rate s)) volume 0 t := by
  apply ac_intervalIntegrable_ae ((P.total_ac ht).mul
    (ac_exp ((integrablePanClock_ac P.rate_integrable 0 t).const_mul 2)))
  filter_upwards [P.twiceTiltedTotal_ae_hasDerivAt] with s hs hmem
  exact hs ((by simpa only [uIcc_of_le ht] using hmem : s ∈ Icc 0 t).1)

theorem total_sub_exp_twice_eq {t : ℝ} (ht : 0 ≤ t) :
    P.total t - Real.exp (-2 * integrablePanClock rate t) =
      Real.exp (-2 * integrablePanClock rate t) *
        (∫ s in (0 : ℝ)..t,
          rate s * P.D s * Real.exp (2 * integrablePanClock rate s)) := by
  rw [P.twiceTiltedTotal_integral ht]
  have he : Real.exp (-2 * integrablePanClock rate t) *
      Real.exp (2 * integrablePanClock rate t) = 1 := by
    rw [← Real.exp_add]
    rw [show -2 * integrablePanClock rate t + 2 * integrablePanClock rate t = 0 by ring,
      Real.exp_zero]
  linear_combination -P.total t * he

theorem exp_twice_le_total {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-2 * integrablePanClock rate t) ≤ P.total t := by
  have hi : 0 ≤ ∫ s in (0 : ℝ)..t,
      rate s * P.D s * Real.exp (2 * integrablePanClock rate s) := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht
    change ∀ᵐ s ∂volume.restrict (Icc 0 t),
      0 ≤ rate s * P.D s * Real.exp (2 * integrablePanClock rate s)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [P.rate_nonneg] with s hs hmem
    exact mul_nonneg (mul_nonneg (hs hmem.1) (P.D_positive s hmem.1).le)
      (Real.exp_pos _).le
  have := P.total_sub_exp_twice_eq ht
  nlinarith [mul_nonneg (Real.exp_pos (-2 * integrablePanClock rate t)).le hi]

theorem exp_twice_lt_total {t : ℝ} (ht : 0 ≤ t)
    (hH : 0 < integrablePanClock rate t) :
    Real.exp (-2 * integrablePanClock rate t) < P.total t := by
  obtain ⟨ε, hε, hD⟩ := P.D_compact_lower_bound t
  have hr : IntervalIntegrable rate volume 0 t :=
    ((P.rate_integrable.mono_set (show uIcc 0 t ⊆ Ici 0 from by
      rw [uIcc_of_le ht]
      exact Icc_subset_Ici_self)).integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hbound : ε * integrablePanClock rate t ≤
      ∫ s in (0 : ℝ)..t,
        rate s * P.D s * Real.exp (2 * integrablePanClock rate s) := by
    rw [integrablePanClock_eq_integral rate ht, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict ht (hr.const_mul ε)
      (P.twiceTiltedTotal_intervalIntegrable ht)
    change ∀ᵐ s ∂volume.restrict (Icc 0 t),
      ε * rate s ≤ rate s * P.D s * Real.exp (2 * integrablePanClock rate s)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [P.rate_nonneg] with s hs hmem
    have he : 1 ≤ Real.exp (2 * integrablePanClock rate s) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num)
        (integrablePanClock_nonneg P.rate_nonneg hmem.1))
    calc
      ε * rate s ≤ rate s * P.D s := by nlinarith [hs hmem.1, hD s hmem]
      _ ≤ rate s * P.D s * Real.exp (2 * integrablePanClock rate s) :=
        le_mul_of_one_le_right (mul_nonneg (hs hmem.1) (P.D_positive s hmem.1).le) he
  have hi : 0 < ∫ s in (0 : ℝ)..t,
      rate s * P.D s * Real.exp (2 * integrablePanClock rate s) :=
    (mul_pos hε hH).trans_le hbound
  have he := P.total_sub_exp_twice_eq ht
  nlinarith [mul_pos (Real.exp_pos (-2 * integrablePanClock rate t)) hi]

end IntegrablePanPreModel

namespace ProperIntegrablePanModel
variable (P : ProperIntegrablePanModel)

theorem firstFlux_lintegral_tail {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal
      (P.pre.diagonalDensity t + 2 * (P.rate t * P.pre.nonDiagonal t))) =
      ENNReal.ofReal (P.pre.total s) := by
  have hac (b : ℝ) (hb : s ≤ b) :
      AbsolutelyContinuousOnInterval P.pre.total s b :=
    (P.pre.total_ac (hs.trans hb)).mono (by
      rw [uIcc_of_le hb, uIcc_of_le (hs.trans hb)]
      exact Icc_subset_Icc_left hs)
  have hd : ∀ᵐ t, s ≤ t → HasDerivAt P.pre.total
      (-(P.pre.diagonalDensity t + 2 * (P.rate t * P.pre.nonDiagonal t))) t := by
    filter_upwards [P.pre.total_ae_hasDerivAt] with t ht hst
    convert! ht (hs.trans hst) using 1
    dsimp [IntegrablePanPreModel.diagonalDensity, IntegrablePanPreModel.nonDiagonal]
    ring
  have hn : ∀ᵐ t, s ≤ t →
      0 ≤ P.pre.diagonalDensity t + 2 * (P.rate t * P.pre.nonDiagonal t) := by
    filter_upwards [P.pre.rate_nonneg] with t ht hst
    have ht0 := hs.trans hst
    exact add_nonneg (mul_nonneg (ht ht0) (P.pre.D_positive t ht0).le)
      (mul_nonneg (by norm_num) (mul_nonneg (ht ht0) (P.pre.nonDiagonal_nonneg ht0)))
  have hm := (P.pre.diagonalDensity_aemeasurable.add
    (P.pre.nonDiagonalFlux_aemeasurable.const_mul 2)).mono_measure
      (Measure.restrict_mono (Ioi_subset_Ioi hs) le_rfl)
  simpa only [sub_zero] using ac_flux_lintegral_Ioi hac hd hn hm P.total_tendsto_zero

theorem jointLaw_square_tail {s : ℝ} (hs : 0 ≤ s) :
    P.pre.jointLaw (Ioi s ×ˢ Ioi s) = ENNReal.ofReal (P.pre.total s) := by
  have hrect : MeasurableSet (Ioi s ×ˢ Ioi s) := measurableSet_Ioi.prod measurableSet_Ioi
  have hd : diagonalDensityLaw P.pre.diagonalDensity (Ioi s ×ˢ Ioi s) =
      ∫⁻ t in Ioi s, ENNReal.ofReal (P.pre.diagonalDensity t) := by
    rw [diagonalDensityLaw, Measure.map_apply (f := fun t : ℝ => (t,t))
      (measurable_id.prodMk measurable_id) hrect]
    have he : (fun t : ℝ => (t,t)) ⁻¹' (Ioi s ×ˢ Ioi s) = Ioi s := by ext t; simp
    rw [he, withDensity_apply _ measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hs)]
  have hu : triangularDensityLaw P.pre.upperDensity (Ioi s ×ˢ Ioi s) =
      ∫⁻ t in Ioi s, ENNReal.ofReal (P.rate t * P.pre.nonDiagonal t) := by
    have he : (Ioi s ×ˢ Ioi s) ∩ upperWedge = (Prod.fst ⁻¹' Ioi s) ∩ upperWedge := by
      ext p
      simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_preimage, upperWedge, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h1.trans h2.2⟩, h2⟩
    calc
      _ = (triangularDensityLaw P.pre.upperDensity).map Prod.fst (Ioi s) := by
        rw [Measure.map_apply measurable_fst measurableSet_Ioi, triangularDensityLaw,
          withDensity_apply _ hrect, withDensity_apply _ (measurable_fst measurableSet_Ioi),
          Measure.restrict_restrict hrect,
          Measure.restrict_restrict (measurable_fst measurableSet_Ioi), he]
      _ = _ := by
        rw [P.triangular_map_fst, withDensity_apply _ measurableSet_Ioi,
          Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hs)]
  have hswap : Prod.swap ⁻¹' (Ioi s ×ˢ Ioi s) = Ioi s ×ˢ Ioi s := by
    ext p
    exact and_comm
  rw [P.pre.jointLaw_eq_regular, regularJointLaw, Measure.add_apply, Measure.add_apply,
    Measure.map_apply (f := Prod.swap) (measurable_snd.prodMk measurable_fst) hrect, hswap, hd, hu]
  rw [← P.firstFlux_lintegral_tail hs]
  have hmδ := P.pre.diagonalDensity_aemeasurable.mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi hs) le_rfl)
  have hma := P.pre.nonDiagonalFlux_aemeasurable.mono_measure
    (Measure.restrict_mono (Ioi_subset_Ioi hs) le_rfl)
  rw [← lintegral_add_left' hmδ.ennreal_ofReal,
    ← lintegral_add_left' (f := fun t => ENNReal.ofReal (P.pre.diagonalDensity t) +
      ENNReal.ofReal (P.rate t * P.pre.nonDiagonal t))
      (hmδ.ennreal_ofReal.add hma.ennreal_ofReal)]
  apply lintegral_congr_ae
  filter_upwards [P.pre.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with t ht hts
  have ht0 := hs.trans hts.le
  have hn := mul_nonneg (ht ht0) (P.pre.nonDiagonal_nonneg ht0)
  have hdn : 0 ≤ P.pre.diagonalDensity t := mul_nonneg (ht ht0) (P.pre.D_positive t ht0).le
  rw [← ENNReal.ofReal_add hdn hn, ← ENNReal.ofReal_add (add_nonneg hdn hn) hn]
  congr 1
  ring

theorem upperDensity_lintegral_later {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hr : 0 ≤ P.rate u) :
    (∫⁻ v in Ioi t, ENNReal.ofReal (P.pre.upperDensity (u,v))) =
      ENNReal.ofReal (P.rate u * P.pre.nonDiagonal u *
        Real.exp (integrablePanClock P.rate u - integrablePanClock P.rate t)) := by
  let c := P.rate u * P.pre.nonDiagonal u *
    Real.exp (integrablePanClock P.rate u - integrablePanClock P.rate t)
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hr (P.pre.nonDiagonal_nonneg hu))
    (Real.exp_pos _).le
  have he (v : ℝ) : P.pre.upperDensity (u,v) = c *
      conditionalPairDensity P.rate (integrablePanClock P.rate) t v := by
    dsimp [IntegrablePanPreModel.upperDensity, conditionalPairDensity, c]
    rw [show integrablePanClock P.rate u - integrablePanClock P.rate v =
      (integrablePanClock P.rate u - integrablePanClock P.rate t) +
      (integrablePanClock P.rate t - integrablePanClock P.rate v) by ring, Real.exp_add]
    ring
  simp_rw [he, ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    integrable_conditionalPair_lintegral_one P.pre.rate_integrable P.pre.rate_nonneg
      P.clock_diverges ht, mul_one]

theorem jointLaw_upper_strip {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P.pre.jointLaw (Ioc s t ×ˢ Ioi t) = ENNReal.ofReal
      (Real.exp (-integrablePanClock P.rate t) *
        (∫ u in s..t, P.rate u * P.pre.nonDiagonal u *
          Real.exp (integrablePanClock P.rate u))) := by
  have ht := hs.trans hst
  have hm : MeasurableSet (Ioc s t ×ˢ Ioi t) := measurableSet_Ioc.prod measurableSet_Ioi
  have hsub : Ioc s t ×ˢ Ioi t ⊆ upperWedge := by
    rintro ⟨u,v⟩ ⟨hu, hv⟩
    exact ⟨hs.trans_lt hu.1, hu.2.trans_lt hv⟩
  have he : P.pre.jointLaw (Ioc s t ×ˢ Ioi t) =
      ∫⁻ u in Ioc s t, ∫⁻ v in Ioi t, ENNReal.ofReal (P.pre.upperDensity (u,v)) := by
    calc
      _ = (P.pre.jointLaw.restrict upperWedge) (Ioc s t ×ˢ Ioi t) := by
        rw [Measure.restrict_apply hm, inter_eq_left.mpr hsub]
      _ = triangularDensityLaw P.pre.upperDensity (Ioc s t ×ˢ Ioi t) := by
        rw [P.pre.jointLaw_eq_regular, regularJointLaw_restrict_upper]
      _ = ∫⁻ z in Ioc s t ×ˢ Ioi t, ENNReal.ofReal (P.pre.upperDensity z) ∂planeVolume := by
        rw [triangularDensityLaw, withDensity_apply _ hm, Measure.restrict_restrict hm,
          inter_eq_left.mpr hsub]
      _ = _ := setLIntegral_prod _ (P.pre.upperDensity_aemeasurable.ennreal_ofReal.mono_measure
        (Measure.restrict_mono hsub le_rfl))
  rw [he]
  have he' : (∫⁻ u in Ioc s t, ∫⁻ v in Ioi t, ENNReal.ofReal (P.pre.upperDensity (u,v))) =
      ∫⁻ u in Ioc s t, ENNReal.ofReal
        (Real.exp (-integrablePanClock P.rate t) *
          (P.rate u * P.pre.nonDiagonal u * Real.exp (integrablePanClock P.rate u))) := by
    apply lintegral_congr_ae
    filter_upwards [P.pre.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioc] with u hu hmem
    rw [P.upperDensity_lintegral_later (hs.trans hmem.1.le) ht
      (hu (hs.trans hmem.1.le))]
    congr 1
    rw [Real.exp_sub, Real.exp_neg]
    ring
  rw [he']
  have hi : IntervalIntegrable (fun u => P.rate u * P.pre.nonDiagonal u *
      Real.exp (integrablePanClock P.rate u)) volume s t :=
    (P.pre.source_intervalIntegrable ht).mono_set (by
      rw [uIcc_of_le hst, uIcc_of_le ht]
      exact Icc_subset_Icc_left hs)
  have hn : ∀ᵐ u ∂volume.restrict (Ioc s t), 0 ≤ P.rate u * P.pre.nonDiagonal u *
      Real.exp (integrablePanClock P.rate u) := by
    filter_upwards [P.pre.rate_nonneg.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioc] with u hu hmem
    exact mul_nonneg (mul_nonneg (hu (hs.trans hmem.1.le))
      (P.pre.nonDiagonal_nonneg (hs.trans hmem.1.le))) (Real.exp_pos _).le
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos (-integrablePanClock P.rate t)).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi.1 hn,
    ← ENNReal.ofReal_mul (Real.exp_pos (-integrablePanClock P.rate t)).le,
    ← intervalIntegral.integral_of_le hst]
  exact ENNReal.ofReal_mul (Real.exp_pos _).le

theorem jointLaw_upper_tail {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P.pre.jointLaw (Ioi s ×ˢ Ioi t) = ENNReal.ofReal
      (P.pre.total s * Real.exp
        (integrablePanClock P.rate s - integrablePanClock P.rate t)) := by
  have ht := hs.trans hst
  have he : Ioi s ×ˢ Ioi t = (Ioi t ×ˢ Ioi t) ∪ (Ioc s t ×ˢ Ioi t) := by
    ext p
    simp only [mem_prod, mem_union, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨hps, hpt⟩
      by_cases h : t < p.1
      · exact Or.inl ⟨h, hpt⟩
      · exact Or.inr ⟨⟨hps, le_of_not_gt h⟩, hpt⟩
    · rintro (⟨hpt, hp2⟩ | ⟨⟨hps, _⟩, hp2⟩)
      · exact ⟨hst.trans_lt hpt, hp2⟩
      · exact ⟨hps, hp2⟩
  have hd : Disjoint (Ioi t ×ˢ Ioi t) (Ioc s t ×ˢ Ioi t) := by
    rw [disjoint_left]
    intro p hp hq
    exact not_lt_of_ge hq.1.2 hp.1
  rw [he, measure_union hd (measurableSet_Ioc.prod measurableSet_Ioi),
    P.jointLaw_square_tail ht, P.jointLaw_upper_strip hs hst]
  have hi := intervalIntegral.integral_interval_sub_left
    (P.pre.source_intervalIntegrable ht) (P.pre.source_intervalIntegrable hs)
  rw [P.pre.source_integral ht, P.pre.source_integral hs] at hi
  have hsource : 0 ≤ ∫ u in s..t, P.rate u * P.pre.nonDiagonal u *
      Real.exp (integrablePanClock P.rate u) := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hst
    change ∀ᵐ u ∂volume.restrict (Icc s t), 0 ≤ P.rate u * P.pre.nonDiagonal u *
      Real.exp (integrablePanClock P.rate u)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [P.pre.rate_nonneg] with u hu hmem
    exact mul_nonneg (mul_nonneg (hu (hs.trans hmem.1))
      (P.pre.nonDiagonal_nonneg (hs.trans hmem.1))) (Real.exp_pos _).le
  rw [← ENNReal.ofReal_add (P.pre.total_positive ht).le
    (mul_nonneg (Real.exp_pos _).le hsource)]
  congr 1
  rw [← hi, Real.exp_sub, Real.exp_neg]
  field_simp
  ring

theorem mutation_marginal_tail {s : ℝ} (hs : 0 ≤ s) :
    (P.pre.jointLaw.map Prod.fst) (Ioi s) =
      ENNReal.ofReal (Real.exp (-integrablePanClock P.rate s)) := by
  rw [P.jointLaw_map_fst, integrable_conditionalPairLaw_tail P.pre.rate_integrable
    P.pre.rate_nonneg P.clock_diverges (s := 0) le_rfl hs,
    integrablePanClock_zero, zero_sub]

theorem jointLaw_tail {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    P.pre.jointLaw (Ioi s ×ˢ Ioi t) = ENNReal.ofReal
      (P.pre.total (min s t) * Real.exp
        (integrablePanClock P.rate (min s t) - integrablePanClock P.rate (max s t))) := by
  by_cases hst : s ≤ t
  · simpa only [min_eq_left hst, max_eq_right hst] using P.jointLaw_upper_tail hs hst
  · have hts := le_of_not_ge hst
    have he : Prod.swap ⁻¹' (Ioi s ×ˢ Ioi t) = Ioi t ×ˢ Ioi s := by
      ext p
      exact and_comm
    calc
      _ = (P.pre.jointLaw.map Prod.swap) (Ioi s ×ˢ Ioi t) := by rw [P.jointLaw_map_swap]
      _ = P.pre.jointLaw (Ioi t ×ˢ Ioi s) := by
        rw [Measure.map_apply (f := Prod.swap) (measurable_snd.prodMk measurable_fst)
          (measurableSet_Ioi.prod measurableSet_Ioi), he]
      _ = _ := by
        simpa only [min_eq_right hts, max_eq_left hts] using P.jointLaw_upper_tail ht hts

theorem jointLaw_tail_ge_product {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (P.pre.jointLaw.map Prod.fst) (Ioi s) *
      (P.pre.jointLaw.map Prod.fst) (Ioi t) ≤ P.pre.jointLaw (Ioi s ×ˢ Ioi t) := by
  rw [P.mutation_marginal_tail hs, P.mutation_marginal_tail ht, P.jointLaw_tail hs ht,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-integrablePanClock P.rate s) * Real.exp (-integrablePanClock P.rate t) =
      Real.exp (-2 * integrablePanClock P.rate (min s t)) * Real.exp
        (integrablePanClock P.rate (min s t) - integrablePanClock P.rate (max s t)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rcases le_total s t with h | h
    · simp only [min_eq_left h, max_eq_right h]; ring
    · simp only [min_eq_right h, max_eq_left h]; ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (P.pre.exp_twice_le_total (le_min hs ht)) (Real.exp_pos _).le

theorem jointLaw_tail_gt_product {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hH : 0 < integrablePanClock P.rate (min s t)) :
    (P.pre.jointLaw.map Prod.fst) (Ioi s) *
      (P.pre.jointLaw.map Prod.fst) (Ioi t) < P.pre.jointLaw (Ioi s ×ˢ Ioi t) := by
  rw [P.mutation_marginal_tail hs, P.mutation_marginal_tail ht, P.jointLaw_tail hs ht,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).2
  have he : Real.exp (-integrablePanClock P.rate s) * Real.exp (-integrablePanClock P.rate t) =
      Real.exp (-2 * integrablePanClock P.rate (min s t)) * Real.exp
        (integrablePanClock P.rate (min s t) - integrablePanClock P.rate (max s t)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rcases le_total s t with h | h
    · simp only [min_eq_left h, max_eq_right h]; ring
    · simp only [min_eq_right h, max_eq_left h]; ring
  rw [he]
  exact mul_lt_mul_of_pos_right (P.pre.exp_twice_lt_total (le_min hs ht) hH) (Real.exp_pos _)

theorem exists_strict_quadrant_threshold :
    ∃ T : ℝ, 0 < T ∧ ∀ s t, T ≤ s → T ≤ t →
      (P.pre.jointLaw.map Prod.fst) (Ioi s) *
        (P.pre.jointLaw.map Prod.fst) (Ioi t) < P.pre.jointLaw (Ioi s ×ˢ Ioi t) := by
  obtain ⟨T, hT, hH⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (P.clock_diverges.eventually (eventually_gt_atTop (0 : ℝ)))).exists
  refine ⟨T, hT, fun s t hs ht => P.jointLaw_tail_gt_product (hT.le.trans hs)
    (hT.le.trans ht) ?_⟩
  exact hH.trans_le (integrablePanClock_monotoneOn P.pre.rate_integrable
    P.pre.rate_nonneg hT.le (hT.le.trans (le_min hs ht)) (le_min hs ht))

end ProperIntegrablePanModel
end Rhone.Statistics.Identifiability
