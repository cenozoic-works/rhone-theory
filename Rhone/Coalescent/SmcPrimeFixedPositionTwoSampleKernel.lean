/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The two-sample SMC′ root-height jump kernel and its reversing law

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory Set
open scoped ENNReal

noncomputable def twoSampleJumpDensity (h a : ℝ) : ℝ :=
  if a < h then (1 - Real.exp (-(2 * a))) / (2 * h)
  else (1 - Real.exp (-(2 * h))) / (2 * h) * Real.exp (-(a - h))

noncomputable def twoSampleSelfMass (h : ℝ) : ℝ :=
  1 / 2 - (1 - Real.exp (-(2 * h))) / (4 * h)

theorem twoSampleJumpDensity_nonneg {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    0 ≤ twoSampleJumpDensity h a := by
  have e1 : Real.exp (-(2 * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have e2 : Real.exp (-(2 * h)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold twoSampleJumpDensity
  split_ifs
  · exact div_nonneg (by linarith) (by linarith)
  · exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (Real.exp_pos _).le

theorem twoSampleSelfMass_nonneg {h : ℝ} (hh : 0 < h) : 0 ≤ twoSampleSelfMass h := by
  have e := Real.add_one_le_exp (-(2 * h))
  unfold twoSampleSelfMass
  have : (1 - Real.exp (-(2 * h))) / (4 * h) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

theorem twoSampleSelfMass_le_one {h : ℝ} (hh : 0 < h) : twoSampleSelfMass h ≤ 1 := by
  have e2 : Real.exp (-(2 * h)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold twoSampleSelfMass
  have : 0 ≤ (1 - Real.exp (-(2 * h))) / (4 * h) := div_nonneg (by linarith) (by linarith)
  linarith

theorem twoSampleJumpDensity_detailed_balance {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    h * Real.exp (-h) * twoSampleJumpDensity h a =
      a * Real.exp (-a) * twoSampleJumpDensity a h := by
  have key : ∀ {x y : ℝ}, 0 < x → 0 < y → x < y →
      y * Real.exp (-y) * twoSampleJumpDensity y x =
        x * Real.exp (-x) * twoSampleJumpDensity x y := by
    intro x y hx hy hxy
    unfold twoSampleJumpDensity
    simp only [hxy, not_lt.mpr hxy.le, ↓reduceIte]
    have he : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    field_simp
  rcases lt_trichotomy a h with hlt | heq | hgt
  · exact key ha hh hlt
  · rw [heq]
  · exact (key hh ha hgt).symm

theorem lintegral_twoSampleJumpDensity_below {h : ℝ} (hh : 0 < h) :
    ∫⁻ a in Ioo 0 h, ENNReal.ofReal ((1 - Real.exp (-(2 * a))) / (2 * h)) =
      ENNReal.ofReal ((h - (1 - Real.exp (-(2 * h))) / 2) / (2 * h)) := by
  have hcont : Continuous (fun a : ℝ => (1 - Real.exp (-(2 * a))) / (2 * h)) := by fun_prop
  have hint : IntegrableOn (fun a : ℝ => (1 - Real.exp (-(2 * a))) / (2 * h)) (Ioo 0 h) :=
    (hcont.integrableOn_Icc (a := 0) (b := h)).mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 h)]
      fun a : ℝ => (1 - Real.exp (-(2 * a))) / (2 * h) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    have e1 : Real.exp (-(2 * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ha.1])
    exact div_nonneg (by linarith) (by linarith)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hh.le]
  congr 1
  have hderiv : ∀ x ∈ uIcc 0 h, HasDerivAt
      (fun a : ℝ => (a + Real.exp (-(2 * a)) / 2) / (2 * h))
      ((1 - Real.exp (-(2 * x))) / (2 * h)) x := by
    intro x _
    have h1 : HasDerivAt (fun a : ℝ => -(2 * a)) (-2) x := by
      have h0 := (hasDerivAt_id' x).const_mul (-2 : ℝ)
      convert h0 using 1
      · funext a
        ring
      · ring
    have h2 := (h1.exp.div_const 2)
    have h3 := ((hasDerivAt_id' x).add h2).div_const (2 * h)
    convert h3 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero, zero_add]
  ring

theorem lintegral_twoSampleJumpDensity_above (h : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ a in Ici h, ENNReal.ofReal (c * Real.exp (-(a - h))) = ENNReal.ofReal c := by
  have hfun : (fun a : ℝ => c * Real.exp (-(a - h))) =
      fun a : ℝ => c * Real.exp h * Real.exp (-a) := by
    funext a
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hint : IntegrableOn (fun a : ℝ => c * Real.exp (-(a - h))) (Ioi h) := by
    rw [hfun]
    exact (integrableOn_exp_neg_Ioi h).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi h)] fun a : ℝ => c * Real.exp (-(a - h)) :=
    Filter.Eventually.of_forall fun a => mul_nonneg hc (Real.exp_pos _).le
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [hfun, integral_const_mul, integral_exp_neg_Ioi, mul_assoc, ← Real.exp_add]
  simp

theorem lintegral_twoSampleJumpDensity {h : ℝ} (hh : 0 < h) :
    ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) =
      ENNReal.ofReal (1 - twoSampleSelfMass h) := by
  have hsplit : Ioi (0 : ℝ) = Ioo 0 h ∪ Ici h := (Ioo_union_Ici_eq_Ioi hh).symm
  have hdisj : Disjoint (Ioo 0 h) (Ici h) :=
    Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx' hx.2
  have e2 : Real.exp (-(2 * h)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have e3 := Real.add_one_le_exp (-(2 * h))
  have hc : 0 ≤ (1 - Real.exp (-(2 * h))) / (2 * h) := div_nonneg (by linarith) (by linarith)
  rw [hsplit, lintegral_union measurableSet_Ici hdisj]
  have h1 : ∫⁻ a in Ioo 0 h, ENNReal.ofReal (twoSampleJumpDensity h a) =
      ∫⁻ a in Ioo 0 h, ENNReal.ofReal ((1 - Real.exp (-(2 * a))) / (2 * h)) :=
    setLIntegral_congr_fun measurableSet_Ioo fun a ha => by
      simp only [twoSampleJumpDensity, ha.2, ↓reduceIte]
  have h2 : ∫⁻ a in Ici h, ENNReal.ofReal (twoSampleJumpDensity h a) =
      ∫⁻ a in Ici h, ENNReal.ofReal
        ((1 - Real.exp (-(2 * h))) / (2 * h) * Real.exp (-(a - h))) :=
    setLIntegral_congr_fun measurableSet_Ici fun a ha => by
      simp only [twoSampleJumpDensity, not_lt.mpr ha, ↓reduceIte]
  rw [h1, h2, lintegral_twoSampleJumpDensity_below hh,
    lintegral_twoSampleJumpDensity_above h hc, ← ENNReal.ofReal_add _ hc]
  · congr 1
    unfold twoSampleSelfMass
    field_simp
    ring
  · apply div_nonneg _ (by linarith)
    linarith

theorem measurable_twoSampleJumpDensity :
    Measurable (fun p : ℝ × ℝ => twoSampleJumpDensity p.1 p.2) := by
  unfold twoSampleJumpDensity
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    (by fun_prop) (by fun_prop)

theorem twoSample_lengthBiased_invariant (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
        (ENNReal.ofReal (twoSampleSelfMass h) * f h +
          ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) * f a) =
      ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) * f h := by
  have hk := measurable_twoSampleJumpDensity
  have hk' : Measurable (fun p : ℝ × ℝ => twoSampleJumpDensity p.2 p.1) :=
    hk.comp measurable_swap
  have hw : Measurable (fun h : ℝ => ENNReal.ofReal (h * Real.exp (-h))) := by fun_prop
  have hinner : Measurable (fun h : ℝ =>
      ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) * f a) :=
    Measurable.lintegral_prod_right'
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (twoSampleJumpDensity p.1 p.2) * f p.2)
      ((ENNReal.measurable_ofReal.comp hk).mul (hf.comp measurable_snd))
  have hself : Measurable (fun h : ℝ => ENNReal.ofReal (twoSampleSelfMass h)) := by
    unfold twoSampleSelfMass
    fun_prop
  have hfirst : Measurable (fun h : ℝ => ENNReal.ofReal (h * Real.exp (-h)) *
      (ENNReal.ofReal (twoSampleSelfMass h) * f h)) := hw.mul (hself.mul hf)
  have hjump : ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
        ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) * f a =
      ∫⁻ a in Ioi 0, ENNReal.ofReal (a * Real.exp (-a)) *
        (ENNReal.ofReal (1 - twoSampleSelfMass a) * f a) := by
    calc ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
          ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) * f a
        = ∫⁻ h in Ioi 0, ∫⁻ a in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
            (ENNReal.ofReal (twoSampleJumpDensity h a) * f a) := by
          refine lintegral_congr fun h => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ∫⁻ a in Ioi 0, ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
            (ENNReal.ofReal (twoSampleJumpDensity h a) * f a) := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact ((hw.comp measurable_fst).mul
            ((ENNReal.measurable_ofReal.comp hk).mul (hf.comp measurable_snd)))
      _ = ∫⁻ a in Ioi 0, ∫⁻ h in Ioi 0, ENNReal.ofReal (a * Real.exp (-a)) * f a *
            ENNReal.ofReal (twoSampleJumpDensity a h) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
          refine setLIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
          have hdb := twoSampleJumpDensity_detailed_balance (mem_Ioi.mp hh) (mem_Ioi.mp ha)
          have hwh : 0 ≤ h * Real.exp (-h) := mul_nonneg (mem_Ioi.mp hh).le (Real.exp_pos _).le
          have hwa : 0 ≤ a * Real.exp (-a) := mul_nonneg (mem_Ioi.mp ha).le (Real.exp_pos _).le
          calc ENNReal.ofReal (h * Real.exp (-h)) *
                (ENNReal.ofReal (twoSampleJumpDensity h a) * f a)
              = ENNReal.ofReal (h * Real.exp (-h) * twoSampleJumpDensity h a) * f a := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul hwh]
            _ = ENNReal.ofReal (a * Real.exp (-a) * twoSampleJumpDensity a h) * f a := by
                rw [hdb]
            _ = ENNReal.ofReal (a * Real.exp (-a)) * f a *
                  ENNReal.ofReal (twoSampleJumpDensity a h) := by
                rw [ENNReal.ofReal_mul hwa]
                ring
      _ = ∫⁻ a in Ioi 0, ENNReal.ofReal (a * Real.exp (-a)) *
            (ENNReal.ofReal (1 - twoSampleSelfMass a) * f a) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
          have hm : Measurable (fun h : ℝ => ENNReal.ofReal (twoSampleJumpDensity a h)) :=
            ENNReal.measurable_ofReal.comp (hk.comp (measurable_const.prodMk measurable_id))
          rw [lintegral_const_mul _ hm, lintegral_twoSampleJumpDensity (mem_Ioi.mp ha)]
          ring
  calc ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
        (ENNReal.ofReal (twoSampleSelfMass h) * f h +
          ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) * f a)
      = (∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
            (ENNReal.ofReal (twoSampleSelfMass h) * f h)) +
          ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
            ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) * f a := by
        rw [← lintegral_add_left hfirst]
        refine lintegral_congr fun h => ?_
        rw [mul_add]
    _ = (∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
            (ENNReal.ofReal (twoSampleSelfMass h) * f h)) +
          ∫⁻ a in Ioi 0, ENNReal.ofReal (a * Real.exp (-a)) *
            (ENNReal.ofReal (1 - twoSampleSelfMass a) * f a) := by rw [hjump]
    _ = ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) * f h := by
        rw [← lintegral_add_left hfirst]
        refine setLIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
        have h0 := twoSampleSelfMass_nonneg (mem_Ioi.mp hh)
        have h1 := twoSampleSelfMass_le_one (mem_Ioi.mp hh)
        rw [← mul_add, ← add_mul, ← ENNReal.ofReal_add h0 (by linarith)]
        simp

end Rhone.Coalescent.SmcPrime
