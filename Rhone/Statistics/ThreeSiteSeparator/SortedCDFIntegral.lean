/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SortedCDFAlgebra
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Joint CDF polynomial under three iid draws, valid with or without atoms -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma below_measurable (x : ℝ) : Measurable (below x) := by
  unfold below
  exact measurable_const.ite measurableSet_Iic measurable_const

lemma below_abs_le_one (x a : ℝ) : |below x a| ≤ 1 := by
  unfold below
  split_ifs <;> norm_num

lemma integral_below (μ : Measure ℝ) (x : ℝ) : ∫ a, below x a ∂μ = μ.real (Iic x) := by
  change (∫ a, (Iic x).indicator (fun _ => (1 : ℝ)) a ∂μ) = _
  rw [integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_one]

lemma triple_below_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (x y z : ℝ) :
    Integrable (fun p : ℝ × ℝ × ℝ => below x p.1*below y p.2.1*below z p.2.2)
      (μ.prod (μ.prod μ)) := by
  have hm : Measurable (fun p : ℝ × ℝ × ℝ => below x p.1*below y p.2.1*below z p.2.2) :=
    (((below_measurable x).comp measurable_fst).mul
      ((below_measurable y).comp (measurable_fst.comp measurable_snd))).mul
      ((below_measurable z).comp (measurable_snd.comp measurable_snd))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  apply ae_of_all
  intro p
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc
    |below x p.1| *|below y p.2.1| *|below z p.2.2| ≤ 1*1*1 :=
      mul_le_mul (mul_le_mul (below_abs_le_one _ _) (below_abs_le_one _ _)
        (abs_nonneg _) (by norm_num)) (below_abs_le_one _ _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

lemma integral_triple_below (μ : Measure ℝ) [SFinite μ] (x y z : ℝ) :
    (∫ p : ℝ × ℝ × ℝ, below x p.1*below y p.2.1*below z p.2.2 ∂μ.prod (μ.prod μ)) =
      μ.real (Iic x)*μ.real (Iic y)*μ.real (Iic z) := by
  simp_rw [mul_assoc]
  rw [integral_prod_mul (fun a => below x a) (fun p : ℝ × ℝ => below y p.1*below z p.2),
    integral_prod_mul (below y) (below z), integral_below, integral_below, integral_below]

lemma integral_cdfTripleExpr (μ : Measure ℝ) [IsFiniteMeasure μ] (x y : ℝ) :
    (∫ p : ℝ × ℝ × ℝ, cdfTripleExpr x y p.1 p.2.1 p.2.2 ∂μ.prod (μ.prod μ)) =
      (3*(μ.real (Iic x))^2*μ.real (Iic y) - (μ.real (Iic y))^3)/2 := by
  have hAB : Integrable (fun p : ℝ × ℝ × ℝ =>
      below x p.1*below x p.2.1*below y p.2.2 +
        below x p.1*below y p.2.1*below x p.2.2) (μ.prod (μ.prod μ)) :=
    (triple_below_integrable μ x x y).add (triple_below_integrable μ x y x)
  have hABC : Integrable (fun p : ℝ × ℝ × ℝ =>
      below x p.1*below x p.2.1*below y p.2.2 +
        below x p.1*below y p.2.1*below x p.2.2 +
        below y p.1*below x p.2.1*below x p.2.2) (μ.prod (μ.prod μ)) :=
    hAB.add (triple_below_integrable μ y x x)
  unfold cdfTripleExpr
  rw [integral_div,
    integral_sub hABC
      (triple_below_integrable μ y y y),
    integral_add hAB
      (triple_below_integrable μ y x x),
    integral_add (triple_below_integrable μ x x y) (triple_below_integrable μ x y x)]
  simp only [integral_triple_below]
  ring

theorem sortedCDF_iid_below (μ : Measure ℝ) [IsFiniteMeasure μ] {x y : ℝ} (hyx : y ≤ x) :
    (∫ p : ℝ × ℝ × ℝ, sortedCDF x y p.1 p.2.1 p.2.2 ∂μ.prod (μ.prod μ)) =
      (3*(μ.real (Iic x))^2*μ.real (Iic y) - (μ.real (Iic y))^3)/2 := by
  simp_rw [sortedCDF_polynomial hyx]
  exact integral_cdfTripleExpr μ x y

theorem sortedCDF_iid_above (μ : Measure ℝ) [IsFiniteMeasure μ] {x y : ℝ} (hxy : x ≤ y) :
    (∫ p : ℝ × ℝ × ℝ, sortedCDF x y p.1 p.2.1 p.2.2 ∂μ.prod (μ.prod μ)) =
      (μ.real (Iic x))^3 := by
  simp_rw [sortedCDF_above hxy]
  rw [integral_triple_below]
  ring

end Rhone.Statistics.ThreeSiteSeparator
