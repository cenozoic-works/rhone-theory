/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GaussianHouseOfCards
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-! # Error bounds for the marginal Gaussian fitness against the focal-locus fitness -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory GaussianHouseOfCards
theorem exp_nonpositive_error (x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x-y| := by
  suffices h : ∀ x y : ℝ, x ≤ y → y ≤ 0 → Real.exp y - Real.exp x ≤ y-x by
    by_cases hxy : x ≤ y
    · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hxy)),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith [h x y hxy hy]
    · have hyx := le_of_not_ge hxy
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hyx)),
        abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact h y x hyx hx
  intro x y hxy hy
  have hu : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy
  have hv : Real.exp (x-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he : Real.exp x = Real.exp y * Real.exp (x-y) := by
    rw [← Real.exp_add]; congr 1; ring
  have hb := Real.one_sub_le_exp_neg (y-x)
  have hh : -(y-x) = x-y := by ring
  rw [hh] at hb
  have hm := mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr hv)
  rw [he]
  nlinarith
theorem gaussian_other_homolog_error (S : ℝ) (hS : 0 < S) (a b : ℝ) :
    |gaussianFitness S (a+b)-gaussianFitness S a| ≤
      (|a| * |b|+b^2/2)/S := by
  have hx : -(a+b)^2/(2*S) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hy : -a^2/(2*S) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have he : -(a+b)^2/(2*S)-(-a^2/(2*S)) = -(2*a*b+b^2)/(2*S) := by ring
  have hp := exp_nonpositive_error _ _ hx hy
  change |gaussianFitness S (a+b)-gaussianFitness S a| ≤ _ at hp
  rw [he, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2*S)] at hp
  apply hp.trans
  have hab := abs_add_le (2*a*b) (b^2)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), abs_of_nonneg (sq_nonneg b)] at hab
  apply (div_le_div_iff₀ (by positivity : 0 < 2*S) hS).mpr
  nlinarith
noncomputable def marginalGaussianFitness (S : ℝ) (μ : Measure ℝ) (a : ℝ) : ℝ :=
  ∫ b, gaussianFitness S (a+b) ∂μ
theorem marginalGaussianFitness_error (S : ℝ) (hS : 0 < S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hab : Integrable (fun b : ℝ => |b|) μ)
    (hb2 : Integrable (fun b : ℝ => b^2) μ) (a : ℝ) :
    |marginalGaussianFitness S μ a - gaussianFitness S a| ≤
      (|a| * (∫ b, |b| ∂μ) + (∫ b, b^2 ∂μ)/2)/S := by
  have hf : Integrable (fun b => gaussianFitness S (a+b)) μ := by
    apply Integrable.of_bound (by unfold gaussianFitness; fun_prop) 1
    exact Filter.Eventually.of_forall (fun b => by
      have h := gaussian_fitness_bounds S hS (a+b)
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1.le] using h.2)
  have hg := hf.sub (integrable_const (gaussianFitness S a))
  have hbound : Integrable (fun b : ℝ => (|a| * |b|+b^2/2)/S) μ :=
    ((hab.const_mul |a|).add (hb2.div_const 2)).div_const S
  have he : marginalGaussianFitness S μ a-gaussianFitness S a =
      ∫ b, (gaussianFitness S (a+b)-gaussianFitness S a) ∂μ := by
    rw [integral_sub hf (integrable_const _)]
    simp only [marginalGaussianFitness, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [he]
  have hi : |∫ b, gaussianFitness S (a+b)-gaussianFitness S a ∂μ| ≤
      ∫ b, |gaussianFitness S (a+b)-gaussianFitness S a| ∂μ :=
    abs_integral_le_integral_abs
  apply hi.trans
  calc
    (∫ b, |gaussianFitness S (a+b)-gaussianFitness S a| ∂μ) ≤
      ∫ b, (|a| * |b|+b^2/2)/S ∂μ := integral_mono hg.abs hbound
        (fun b => gaussian_other_homolog_error S hS a b)
    _ = _ := by
      rw [integral_div, integral_add (hab.const_mul |a|) (hb2.div_const 2),
        integral_const_mul, integral_div]
end Rhone.MarkovChain.DiploidMarginalSelection
