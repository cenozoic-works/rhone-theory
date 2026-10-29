/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ContinuousTimeGenealogy.Exp

/-! # Poisson marks on a branch: the first mark, and the superposition of the two loci -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTimeGenealogy

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem expMeasure_Ioi {r h : ℝ} (hr : 0 < r) (hh : 0 ≤ h) :
    expMeasure r (Ioi h) = ENNReal.ofReal (Real.exp (-(r * h))) := by
  have hp : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hIic : expMeasure r (Iic h) = ENNReal.ofReal (1 - Real.exp (-(r * h))) := by
    rw [← ofReal_cdf (expMeasure r) h, cdf_expMeasure_eq hr, ite_eq_left hh]
  have hle : Real.exp (-(r * h)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, hIic,
    ENNReal.ofReal_sub _ (Real.exp_nonneg _), ENNReal.ofReal_one]
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top (ENNReal.ofReal_le_one.2 hle)

theorem expMeasure_Ioi_of_neg {r h : ℝ} (hr : 0 < r) (hh : h < 0) :
    expMeasure r (Ioi h) = 1 := by
  have hp : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hIic : expMeasure r (Iic h) = 0 := by
    rw [← ofReal_cdf (expMeasure r) h, cdf_expMeasure_eq hr, ite_eq_right (not_le.2 hh),
      ENNReal.ofReal_zero]
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, hIic,
    tsub_zero]

theorem expMeasure_Iic_le {r h : ℝ} (hr : 0 < r) (hh : 0 ≤ h) :
    expMeasure r (Iic h) ≤ ENNReal.ofReal (r * h) := by
  have hp : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hIic : expMeasure r (Iic h) = ENNReal.ofReal (1 - Real.exp (-(r * h))) := by
    rw [← ofReal_cdf (expMeasure r) h, cdf_expMeasure_eq hr, ite_eq_left hh]
  have hexp : 1 - Real.exp (-(r * h)) ≤ r * h := by
    have := Real.add_one_le_exp (-(r * h))
    linarith
  rw [hIic]
  exact ENNReal.ofReal_le_ofReal hexp

theorem map_min_expMeasure {rA rB : ℝ} (hA : 0 < rA) (hB : 0 < rB) :
    ((expMeasure rA).prod (expMeasure rB)).map (fun p : ℝ × ℝ => min p.1 p.2)
      = expMeasure (rA + rB) := by
  have hpA : IsProbabilityMeasure (expMeasure rA) := isProbabilityMeasure_expMeasure hA
  have hpB : IsProbabilityMeasure (expMeasure rB) := isProbabilityMeasure_expMeasure hB
  have hpS : IsProbabilityMeasure (expMeasure (rA + rB)) :=
    isProbabilityMeasure_expMeasure (by linarith)
  have hmeas : Measurable fun p : ℝ × ℝ => min p.1 p.2 := by fun_prop
  have hmap : IsProbabilityMeasure
      (((expMeasure rA).prod (expMeasure rB)).map fun p : ℝ × ℝ => min p.1 p.2) :=
    (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance
  have hpre : ∀ a : ℝ,
      (fun p : ℝ × ℝ => min p.1 p.2) ⁻¹' Ioi a = (Ioi a) ×ˢ (Ioi a) := by
    intro a
    ext p
    simp
  have key : ∀ a : ℝ,
      (((expMeasure rA).prod (expMeasure rB)).map fun p : ℝ × ℝ => min p.1 p.2) (Ioi a)
        = expMeasure (rA + rB) (Ioi a) := by
    intro a
    rw [Measure.map_apply hmeas measurableSet_Ioi, hpre a, Measure.prod_prod]
    rcases le_or_gt 0 a with ha | ha
    · rw [expMeasure_Ioi hA ha, expMeasure_Ioi hB ha, expMeasure_Ioi (by linarith) ha,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    · rw [expMeasure_Ioi_of_neg hA ha, expMeasure_Ioi_of_neg hB ha,
        expMeasure_Ioi_of_neg (by linarith) ha, one_mul]
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ, measure_univ, key a]

theorem map_min_expMeasure_Ioi {rA rB h : ℝ} (hA : 0 < rA) (hB : 0 < rB) (hh : 0 ≤ h) :
    ((expMeasure rA).prod (expMeasure rB)).map (fun p : ℝ × ℝ => min p.1 p.2) (Ioi h)
      = ENNReal.ofReal (Real.exp (-((rA + rB) * h))) := by
  rw [map_min_expMeasure hA hB, expMeasure_Ioi (by linarith) hh]

theorem exponentialPDF_mul_exp {rA rB : ℝ} (hA : 0 < rA) (hB : 0 < rB) (x : ℝ) :
    exponentialPDF rA x * ENNReal.ofReal (Real.exp (-(rB * x)))
      = ENNReal.ofReal (rA / (rA + rB)) * exponentialPDF (rA + rB) x := by
  have hs : 0 < rA + rB := by linarith
  rcases le_or_gt 0 x with hx | hx
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hne : rA + rB ≠ 0 := ne_of_gt hs
    have h1 : rA / (rA + rB) * ((rA + rB) * Real.exp (-((rA + rB) * x)))
        = rA * Real.exp (-((rA + rB) * x)) := by field_simp
    rw [h1, mul_assoc, ← Real.exp_add,
      show -(rA * x) + -(rB * x) = -((rA + rB) * x) from by ring]
  · rw [exponentialPDF_of_neg hx, exponentialPDF_of_neg hx, zero_mul, mul_zero]

theorem prob_first_mark_A {rA rB : ℝ} (hA : 0 < rA) (hB : 0 < rB) :
    ((expMeasure rA).prod (expMeasure rB)) {p : ℝ × ℝ | p.1 < p.2}
      = ENNReal.ofReal (rA / (rA + rB)) := by
  have hpA : IsProbabilityMeasure (expMeasure rA) := isProbabilityMeasure_expMeasure hA
  have hpB : IsProbabilityMeasure (expMeasure rB) := isProbabilityMeasure_expMeasure hB
  have hs : 0 < rA + rB := by linarith
  have hms : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
  rw [Measure.prod_apply hms]
  have hpre : ∀ x : ℝ, Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 < p.2} = Ioi x := by
    intro x
    ext y
    simp
  simp only [hpre]
  have hae : (∫⁻ x, expMeasure rB (Ioi x) ∂(expMeasure rA))
      = ∫⁻ x, ENNReal.ofReal (Real.exp (-(rB * x))) ∂(expMeasure rA) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_expMeasure hA] with x hx
    exact expMeasure_Ioi hB hx
  rw [hae, lintegral_expMeasure rA (by fun_prop),
    lintegral_congr (exponentialPDF_mul_exp hA hB),
    lintegral_const_mul _ (measurable_exponentialPDF (rA + rB)),
    lintegral_exponentialPDF_eq_one hs, mul_one]

end Rhone.Coalescent.ContinuousTimeGenealogy
