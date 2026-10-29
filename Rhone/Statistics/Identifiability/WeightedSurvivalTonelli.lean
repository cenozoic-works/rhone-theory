/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Weighted survival primitives and Tonelli identities for exponential responses -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace Rhone.Statistics.Identifiability

noncomputable def weightedLowerPrimitive (w : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi 0, if s < x then w s else 0

theorem weightedLowerPrimitive_measurable {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    Measurable (weightedLowerPrimitive w) := by
  apply Measurable.lintegral_prod_right
  exact (hw.comp measurable_snd).ite
    (measurableSet_lt measurable_snd measurable_fst) measurable_const

theorem weightedLowerPrimitive_lintegral_fst
    (μ : Measure (ℝ × ℝ)) [SFinite μ]
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    (∫⁻ p, weightedLowerPrimitive w p.1 ∂μ) =
      ∫⁻ s in Ioi 0, w s * (μ.map Prod.fst) (Ioi s) := by
  unfold weightedLowerPrimitive
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro s
    rw [Measure.map_apply measurable_fst measurableSet_Ioi]
    have h : (fun p : ℝ × ℝ => if s < p.1 then w s else 0) =
        (Prod.fst ⁻¹' Ioi s).indicator (fun _ => w s) := by
      funext p
      simp only [Set.indicator, mem_preimage, mem_Ioi]
    rw [h, lintegral_indicator (measurableSet_Ioi.preimage measurable_fst)]
    simp
  · exact ((hw.comp measurable_snd).ite
      (measurableSet_lt measurable_snd measurable_fst.fst) measurable_const).aemeasurable

theorem weightedLowerPrimitive_lintegral_prod
    (μ : Measure (ℝ × ℝ)) [SFinite μ]
    {w v : ℝ → ℝ≥0∞} (hw : Measurable w) (hv : Measurable v) :
    (∫⁻ p, weightedLowerPrimitive w p.1 * weightedLowerPrimitive v p.2 ∂μ) =
      ∫⁻ st, w st.1 * v st.2 * μ (Ioi st.1 ×ˢ Ioi st.2)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hsection (p : ℝ × ℝ) :
      weightedLowerPrimitive w p.1 * weightedLowerPrimitive v p.2 =
        ∫⁻ st, (if st.1 < p.1 then w st.1 else 0) *
          (if st.2 < p.2 then v st.2 else 0)
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    exact (lintegral_prod_mul
      (hw.ite (measurableSet_lt measurable_id measurable_const) measurable_const).aemeasurable
      (hv.ite (measurableSet_lt measurable_id measurable_const) measurable_const).aemeasurable).symm
  simp_rw [hsection]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro st
    have h : (fun p : ℝ × ℝ =>
        (if st.1 < p.1 then w st.1 else 0) * (if st.2 < p.2 then v st.2 else 0)) =
        (Ioi st.1 ×ˢ Ioi st.2).indicator (fun _ => w st.1 * v st.2) := by
      funext p
      by_cases h₁ : st.1 < p.1 <;> by_cases h₂ : st.2 < p.2 <;>
        simp [h₁, h₂, Set.indicator, mem_prod]
    rw [h, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioi)]
    simp
  · exact (((hw.comp measurable_snd.fst).ite
      (measurableSet_lt measurable_snd.fst measurable_fst.fst) measurable_const).mul
      ((hv.comp measurable_snd.snd).ite
        (measurableSet_lt measurable_snd.snd measurable_fst.snd)
        measurable_const)).aemeasurable

theorem measurable_jointSurvival (μ : Measure (ℝ × ℝ)) [SFinite μ] :
    Measurable (fun st : ℝ × ℝ => μ (Ioi st.1 ×ˢ Ioi st.2)) := by
  have hi : Measurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      if z.1.1 < z.2.1 ∧ z.1.2 < z.2.2 then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite
      ((measurableSet_lt measurable_fst.fst measurable_snd.fst).inter
        (measurableSet_lt measurable_fst.snd measurable_snd.snd)) measurable_const
  convert hi.lintegral_prod_right' (ν := μ) using 1
  funext st
  have h : (fun p : ℝ × ℝ =>
      if st.1 < p.1 ∧ st.2 < p.2 then (1 : ℝ≥0∞) else 0) =
      (Ioi st.1 ×ˢ Ioi st.2).indicator (fun _ => 1) := by
    funext p
    simp only [Set.indicator, mem_prod, mem_Ioi]
  rw [h, lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioi)]
  simp

theorem measurable_marginalSurvival (ν : Measure ℝ) [SFinite ν] :
    Measurable (fun s : ℝ => ν (Ioi s)) := by
  have hi : Measurable (fun z : ℝ × ℝ =>
      if z.1 < z.2 then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const
  convert hi.lintegral_prod_right' (ν := ν) using 1
  funext s
  have h : (fun x : ℝ => if s < x then (1 : ℝ≥0∞) else 0) =
      (Ioi s).indicator (fun _ => 1) := by
    funext x
    simp only [Set.indicator, mem_Ioi]
  rw [h, lintegral_indicator measurableSet_Ioi]
  simp

theorem weightedLowerPrimitive_eq_lintegral_Ioo (w : ℝ → ℝ≥0∞) (x : ℝ) :
    weightedLowerPrimitive w x = ∫⁻ s in Ioo 0 x, w s := by
  unfold weightedLowerPrimitive
  have h : (fun s : ℝ => if s < x then w s else 0) = (Iio x).indicator w := by
    funext s
    simp only [Set.indicator, mem_Iio]
  rw [h, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio x ∩ Ioi (0 : ℝ) = Ioo 0 x := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
  rw [hs]

theorem weightedLowerPrimitive_exponential {L k x : ℝ}
    (hL : 0 ≤ L) (hk : 0 ≤ k) (hx : 0 ≤ x) :
    weightedLowerPrimitive (fun s => ENNReal.ofReal (L * k * Real.exp (-k * s))) x =
      ENNReal.ofReal (L * (1 - Real.exp (-k * x))) := by
  have hc : Continuous (fun s : ℝ => L * k * Real.exp (-k * s)) := by fun_prop
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => L * (1 - Real.exp (-k * s)))
      (L * k * Real.exp (-k * t)) t := by
    convert! ((((hasDerivAt_id t).const_mul (-k)).exp).const_sub 1).const_mul L using 1
    simp only [id_eq]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 x)
  simp only [mul_zero, Real.exp_zero, sub_self, mul_zero, sub_zero] at he
  rw [weightedLowerPrimitive_eq_lintegral_Ioo,
    Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := x)),
    ← ofReal_integral_eq_lintegral_ofReal (hc.intervalIntegrable 0 x).1
      (ae_of_all _ (fun s => mul_nonneg (mul_nonneg hL hk) (Real.exp_pos _).le)),
    ← intervalIntegral.integral_of_le hx, he]

theorem weightedLowerPrimitive_lintegral_quadrant
    (μ : Measure (ℝ × ℝ)) [SFinite μ]
    {w v : ℝ → ℝ≥0∞} (hw : Measurable w) (hv : Measurable v) :
    (∫⁻ p, weightedLowerPrimitive w p.1 * weightedLowerPrimitive v p.2 ∂μ) =
      ∫⁻ st in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        w st.1 * v st.2 * μ (Ioi st.1 ×ˢ Ioi st.2) := by
  simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using
    weightedLowerPrimitive_lintegral_prod μ hw hv

theorem exponentialResponse_lintegral_fst
    (μ : Measure (ℝ × ℝ)) [SFinite μ] {L k : ℝ}
    (hL : 0 ≤ L) (hk : 0 ≤ k) (hx : ∀ᵐ p ∂μ, 0 ≤ p.1) :
    (∫⁻ p, ENNReal.ofReal (L * (1 - Real.exp (-k * p.1))) ∂μ) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (L * k * Real.exp (-k * s)) *
        (μ.map Prod.fst) (Ioi s) := by
  rw [← weightedLowerPrimitive_lintegral_fst μ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hx] with p hp
  exact (weightedLowerPrimitive_exponential hL hk hp).symm

theorem exponentialResponse_lintegral_product
    (μ : Measure (ℝ × ℝ)) [SFinite μ] {L k : ℝ}
    (hL : 0 ≤ L) (hk : 0 ≤ k)
    (hx : ∀ᵐ p ∂μ, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (∫⁻ p, ENNReal.ofReal
      (L^2 * (1 - Real.exp (-k * p.1)) * (1 - Real.exp (-k * p.2))) ∂μ) =
      ∫⁻ st in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal (L * k * Real.exp (-k * st.1)) *
        ENNReal.ofReal (L * k * Real.exp (-k * st.2)) *
        μ (Ioi st.1 ×ˢ Ioi st.2) := by
  rw [← weightedLowerPrimitive_lintegral_quadrant μ
    (w := fun s => ENNReal.ofReal (L * k * Real.exp (-k * s)))
    (v := fun s => ENNReal.ofReal (L * k * Real.exp (-k * s))) (by fun_prop) (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hx] with p hp
  rw [weightedLowerPrimitive_exponential hL hk hp.1,
    weightedLowerPrimitive_exponential hL hk hp.2]
  have hn : 0 ≤ L * (1 - Real.exp (-k * p.1)) := by
    apply mul_nonneg hL
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hk hp.1]
  rw [← ENNReal.ofReal_mul hn]
  congr 1
  ring

end Rhone.Statistics.Identifiability
