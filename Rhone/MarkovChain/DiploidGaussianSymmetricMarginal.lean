/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianSymmetricInteraction
/-! # Marginal Gaussian fitness error for a symmetric homolog law -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory GaussianHouseOfCards

theorem gaussianHomolog_integrable (S : ℝ) (hS : 0 < S) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) : Integrable (fun b => gaussianFitness S (a+b)) μ := by
  apply Integrable.of_bound (by unfold gaussianFitness; fun_prop) 1
  exact Filter.Eventually.of_forall (fun b => by
    have hb := gaussian_fitness_bounds S hS (a+b)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1.le] using hb.2)

theorem marginalGaussianFitness_zero_pos (S : ℝ) (hS : 0 < S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : 0 < marginalGaussianFitness S μ 0 := by
  exact integral_exp_pos (gaussianHomolog_integrable S hS μ 0)

theorem symmetric_marginalGaussianFitness_error (S : ℝ) (hS : 0 < S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun b => -b) = μ)
    (hb2 : Integrable (fun b : ℝ => b ^ 2) μ) (a : ℝ) :
    |marginalGaussianFitness S μ a-gaussianFitness S a*marginalGaussianFitness S μ 0| ≤
      a ^ 2*(∫ b, b ^ 2 ∂μ)/(2*S ^ 2) := by
  have hp := gaussianHomolog_integrable S hS μ a
  have hb : Integrable (fun b => gaussianFitness S b) μ := by
    simpa only [zero_add] using gaussianHomolog_integrable S hS μ 0
  have hm : Integrable (fun b => gaussianFitness S (a-b)) μ := by
    apply Integrable.of_bound (by unfold gaussianFitness; fun_prop) 1
    exact Filter.Eventually.of_forall (fun b => by
      have h := gaussian_fitness_bounds S hS (a-b)
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1.le] using h.2)
  have hmeas : Measurable (fun b : ℝ => gaussianFitness S (a+b)) := by
    unfold gaussianFitness; fun_prop
  have hminus : (∫ b, gaussianFitness S (a-b) ∂μ) = marginalGaussianFitness S μ a := by
    have h := integral_map (by fun_prop : AEMeasurable (fun b : ℝ => -b) μ)
      hmeas.aestronglyMeasurable
    rw [hsym] at h
    exact h.symm
  have hg : Integrable (fun b => (gaussianFitness S (a+b)+gaussianFitness S (a-b))/2-
      gaussianFitness S a*gaussianFitness S b) μ := by
    exact ((hp.add hm).div_const 2).sub (hb.const_mul (gaussianFitness S a))
  have hk := (hb2.const_mul (a ^ 2)).div_const (2*S ^ 2)
  have havg : Integrable (fun b => (gaussianFitness S (a+b)+gaussianFitness S (a-b))/2) μ :=
    (hp.add hm).div_const 2
  have hex : marginalGaussianFitness S μ a-gaussianFitness S a*marginalGaussianFitness S μ 0 =
      ∫ b, (gaussianFitness S (a+b)+gaussianFitness S (a-b))/2-
        gaussianFitness S a*gaussianFitness S b ∂μ := by
    rw [integral_sub havg (hb.const_mul _), integral_div,
      integral_add hp hm, integral_const_mul, hminus]
    simp only [marginalGaussianFitness, zero_add]
    ring
  rw [hex]
  calc
    _ ≤ ∫ b, |(gaussianFitness S (a+b)+gaussianFitness S (a-b))/2-
        gaussianFitness S a*gaussianFitness S b| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ b, a ^ 2*b ^ 2/(2*S ^ 2) ∂μ := integral_mono hg.abs hk (fun b => by
      have h := gaussian_symmetric_interaction_error S hS a b
      rw [abs_of_nonneg h.1]
      exact h.2)
    _ = _ := by rw [integral_div, integral_const_mul]

end Rhone.MarkovChain.DiploidMarginalSelection
