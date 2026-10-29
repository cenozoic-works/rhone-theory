/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianSymmetricMarginal
/-! # Relative Gaussian marginal selection costs derived from the other-homolog law -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory GaussianHouseOfCards

noncomputable def marginalGaussianSelectionCost (S : ℝ) (μ : Measure ℝ) (a : ℝ) : ℝ :=
  1-marginalGaussianFitness S μ a/marginalGaussianFitness S μ 0

theorem gaussian_selection_cost_lower (S : ℝ) (hS : 0 < S) (a : ℝ)
    (haS : a ^ 2 ≤ 2 * S) : a ^ 2/(4*S) ≤ 1-gaussianFitness S a := by
  let x := a ^ 2/(2 * S)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := (div_le_one (by positivity : 0 < 2 * S)).mpr haS
  have he : Real.exp (-x) ≤ 1/(x+1) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < x+1) (Real.add_one_le_exp x)
    simpa only [one_div, Real.exp_neg] using hh
  have hd : x/2 ≤ x/(x+1) :=
    div_le_div_of_nonneg_left hx0 (by positivity) (by linarith)
  have hid : x/(x+1) = 1-1/(x+1) := by field_simp; ring
  have hl : x/2 ≤ 1-Real.exp (-x) := by rw [hid] at hd; linarith
  calc
    a ^ 2/(4*S) = x/2 := by dsimp [x]; ring
    _ ≤ 1-Real.exp (-x) := hl
    _ = 1-gaussianFitness S a := by simp only [x, gaussianFitness, neg_div]

theorem marginalGaussianSelectionCost_relative_error (S : ℝ) (hS : 0 < S)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun b => -b) = μ)
    (hb2 : Integrable (fun b : ℝ => b ^ 2) μ) (a : ℝ)
    (ha0 : 0 < a ^ 2) (haS : a ^ 2 ≤ 2 * S) :
    |marginalGaussianSelectionCost S μ a/(1-gaussianFitness S a)-1| ≤
      2*(∫ b, b ^ 2 ∂μ)/(S*marginalGaussianFitness S μ 0) := by
  have hg0 := marginalGaussianFitness_zero_pos S hS μ
  have hd := gaussian_selection_cost_lower S hS a haS
  have hd0 : 0 < 1-gaussianFitness S a := lt_of_lt_of_le (by positivity) hd
  have hm0 : 0 ≤ ∫ b, b ^ 2 ∂μ := integral_nonneg (fun b => sq_nonneg b)
  have herr := symmetric_marginalGaussianFitness_error S hS μ hsym hb2 a
  have hid : marginalGaussianSelectionCost S μ a/(1-gaussianFitness S a)-1 =
      -(marginalGaussianFitness S μ a-gaussianFitness S a*marginalGaussianFitness S μ 0)/
        (marginalGaussianFitness S μ 0*(1-gaussianFitness S a)) := by
    unfold marginalGaussianSelectionCost
    field_simp [ne_of_gt hg0, ne_of_gt hd0]
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos (mul_pos hg0 hd0)]
  apply (div_le_iff₀ (mul_pos hg0 hd0)).mpr
  calc
    _ ≤ a ^ 2*(∫ b, b ^ 2 ∂μ)/(2 * S ^ 2) := herr
    _ = (2*(∫ b, b ^ 2 ∂μ)/S)*(a ^ 2/(4*S)) := by ring
    _ ≤ (2*(∫ b, b ^ 2 ∂μ)/S)*(1-gaussianFitness S a) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by field_simp

end Rhone.MarkovChain.DiploidMarginalSelection
