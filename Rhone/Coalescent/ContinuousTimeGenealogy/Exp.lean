/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # The two moments of an exponential holding time -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTimeGenealogy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (exponentialPDF r) := rfl

theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal

theorem lintegral_expMeasure (r : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(expMeasure r) = ∫⁻ x, exponentialPDF r x * g x := by
  rw [expMeasure_eq_withDensity, lintegral_withDensity_eq_lintegral_mul _
    (measurable_exponentialPDF r) hg]
  rfl

theorem ae_nonneg_expMeasure {r : ℝ} (hr : 0 < r) : ∀ᵐ x ∂(expMeasure r), 0 ≤ x := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [ae_iff]
  have hset : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext x; simp
  rw [hset, expMeasure_eq_withDensity, withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos le_rfl

theorem integral_exp_neg_mul_id : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x = 1 := by
  have hcongr : ∀ x ∈ Ioi (0 : ℝ), Real.exp (-x) * x ^ ((2 : ℝ) - 1) = Real.exp (-x) * x := by
    intro x _
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have h := Real.Gamma_eq_integral (s := 2) (by norm_num)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr] at h
  rw [← h]
  simp

theorem integral_exp_neg_mul_sq : ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ 2 = 2 := by
  have hcongr : ∀ x ∈ Ioi (0 : ℝ), Real.exp (-x) * x ^ ((3 : ℝ) - 1) = Real.exp (-x) * x ^ 2 := by
    intro x hx
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h := Real.Gamma_eq_integral (s := 3) (by norm_num)
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr] at h
  rw [← h]
  simp

theorem integrableOn_exp_neg_mul_id :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent (s := 2) (by norm_num)).congr_fun ?_ measurableSet_Ioi
  intro x _
  change Real.exp (-x) * x ^ ((2 : ℝ) - 1) = Real.exp (-x) * x
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

theorem integrableOn_exp_neg_mul_sq :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ 2) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent (s := 3) (by norm_num)).congr_fun ?_ measurableSet_Ioi
  intro x _
  change Real.exp (-x) * x ^ ((3 : ℝ) - 1) = Real.exp (-x) * x ^ 2
  rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

noncomputable def expOne : Measure ℝ := expMeasure 1

instance isProbabilityMeasure_expOne : IsProbabilityMeasure expOne :=
  isProbabilityMeasure_expMeasure one_pos

theorem expOne_integrand (g : ℝ → ℝ≥0∞) (hg : ∀ x ≤ 0, g x = 0) (x : ℝ) :
    exponentialPDF 1 x * g x = (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp (-y))
      * g y) x := by
  rcases lt_or_ge (0 : ℝ) x with hx | hx
  · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hx), exponentialPDF_eq, ite_eq_left (le_of_lt hx)]
    norm_num
  · rw [Set.indicator_of_notMem (by simpa using hx), hg x hx, mul_zero]

theorem lintegral_id_expOne : ∫⁻ x, ENNReal.ofReal x ∂expOne = 1 := by
  have hg : ∀ x ≤ (0 : ℝ), ENNReal.ofReal x = 0 := fun x hx => by
    simpa using ENNReal.ofReal_eq_zero.2 hx
  rw [expOne, lintegral_expMeasure (g := fun x : ℝ => ENNReal.ofReal x) 1 (by fun_prop)]
  rw [lintegral_congr (expOne_integrand _ hg), lintegral_indicator measurableSet_Ioi]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-x)) * ENNReal.ofReal x
      = ENNReal.ofReal (Real.exp (-x) * x) :=
    fun x _ => (ENNReal.ofReal_mul (Real.exp_nonneg _)).symm
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
    ← ofReal_integral_eq_lintegral_ofReal integrableOn_exp_neg_mul_id
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        mul_nonneg (Real.exp_nonneg _) (le_of_lt hx)),
    integral_exp_neg_mul_id, ENNReal.ofReal_one]

theorem lintegral_sq_expOne :
    ∫⁻ x, ENNReal.ofReal x * ENNReal.ofReal x ∂expOne = 2 := by
  have hg : ∀ x ≤ (0 : ℝ), ENNReal.ofReal x * ENNReal.ofReal x = 0 := fun x hx => by
    simp [ENNReal.ofReal_eq_zero.2 hx]
  rw [expOne, lintegral_expMeasure
    (g := fun x : ℝ => ENNReal.ofReal x * ENNReal.ofReal x) 1 (by fun_prop)]
  rw [lintegral_congr (expOne_integrand _ hg), lintegral_indicator measurableSet_Ioi]
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-x)) * (ENNReal.ofReal x * ENNReal.ofReal x)
        = ENNReal.ofReal (Real.exp (-x) * x ^ 2) := by
    intro x hx
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), sq, ENNReal.ofReal_mul (le_of_lt hx)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
    ← ofReal_integral_eq_lintegral_ofReal integrableOn_exp_neg_mul_sq
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x _ =>
        mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)),
    integral_exp_neg_mul_sq]
  norm_num

theorem map_div_expOne {r : ℝ} (hr : 0 < r) :
    expOne.map (fun x => x / r) = expMeasure r := by
  have h1 : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h2 : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hmeas : Measurable fun x : ℝ => x / r := by fun_prop
  have hmap : IsProbabilityMeasure (expOne.map fun x => x / r) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  refine Measure.ext_of_Iic _ _ fun a => ?_
  have hpre : (fun x : ℝ => x / r) ⁻¹' Iic a = Iic (a * r) := by
    ext x
    simp [Set.mem_Iic, div_le_iff₀ hr]
  rw [Measure.map_apply hmeas measurableSet_Iic, hpre, ← ofReal_cdf (expMeasure r) a, expOne,
    ← ofReal_cdf (expMeasure 1) (a * r), cdf_expMeasure_eq one_pos, cdf_expMeasure_eq hr]
  rcases le_or_gt (0 : ℝ) a with ha | ha
  · rw [ite_eq_left ha, ite_eq_left (mul_nonneg ha (le_of_lt hr))]
    ring_nf
  · rw [ite_eq_right (not_le.2 ha), ite_eq_right (not_le.2 (mul_neg_of_neg_of_pos ha hr))]

theorem lintegral_expMeasure_of_map {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂(expMeasure r) = ∫⁻ x, g (x / r) ∂expOne := by
  rw [← map_div_expOne hr, lintegral_map hg (by fun_prop)]

theorem lintegral_id_expMeasure {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal x ∂(expMeasure r) = ENNReal.ofReal r⁻¹ := by
  rw [lintegral_expMeasure_of_map hr (by fun_prop)]
  have hpt : ∀ x : ℝ, ENNReal.ofReal (x / r) = ENNReal.ofReal x * ENNReal.ofReal r⁻¹ := by
    intro x
    rw [div_eq_mul_inv, ENNReal.ofReal_mul' (le_of_lt (inv_pos.2 hr))]
  rw [lintegral_congr hpt, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_id_expOne,
    one_mul]

theorem lintegral_sq_expMeasure {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal x * ENNReal.ofReal x ∂(expMeasure r)
      = 2 * ENNReal.ofReal r⁻¹ * ENNReal.ofReal r⁻¹ := by
  rw [lintegral_expMeasure_of_map hr (by fun_prop)]
  have hpt : ∀ x : ℝ, ENNReal.ofReal (x / r) * ENNReal.ofReal (x / r)
      = (ENNReal.ofReal x * ENNReal.ofReal x) * (ENNReal.ofReal r⁻¹ * ENNReal.ofReal r⁻¹) := by
    intro x
    rw [div_eq_mul_inv, ENNReal.ofReal_mul' (le_of_lt (inv_pos.2 hr))]
    ring
  rw [lintegral_congr hpt, lintegral_mul_const' _ _
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), lintegral_sq_expOne,
    mul_assoc]

theorem lintegral_sq_expMeasure_eq_two_mul_sq {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal x * ENNReal.ofReal x ∂(expMeasure r)
      = 2 * ((∫⁻ x, ENNReal.ofReal x ∂(expMeasure r))
        * ∫⁻ x, ENNReal.ofReal x ∂(expMeasure r)) := by
  rw [lintegral_sq_expMeasure hr, lintegral_id_expMeasure hr, mul_assoc]

end Rhone.Coalescent.ContinuousTimeGenealogy
