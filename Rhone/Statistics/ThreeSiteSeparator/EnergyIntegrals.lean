/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.EnergyAlgebra
public import Rhone.Statistics.ThreeSiteSeparator.PrimitiveIdentities

/-! # Integrated linear and quadratic terms in the CDF energy identity -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma integral_three_terms {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (a b c : ℝ) :
    (∫ x in (0 : ℝ)..1, a*f x - b*g x + c*h x) =
      a*(∫ x in (0 : ℝ)..1, f x) - b*(∫ x in (0 : ℝ)..1, g x) +
        c*(∫ x in (0 : ℝ)..1, h x) := by
  have hA : IntervalIntegrable (fun x => a*f x) volume 0 1 :=
    (show Continuous (fun x => a*f x) by fun_prop).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun x => b*g x) volume 0 1 :=
    (show Continuous (fun x => b*g x) by fun_prop).intervalIntegrable _ _
  have hC : IntervalIntegrable (fun x => c*h x) volume 0 1 :=
    (show Continuous (fun x => c*h x) by fun_prop).intervalIntegrable _ _
  have hAB : IntervalIntegrable (fun x => a*f x - b*g x) volume 0 1 :=
    (show Continuous (fun x => a*f x - b*g x) by fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hAB hC, intervalIntegral.integral_sub hA hB]
  simp only [intervalIntegral.integral_const_mul]

lemma integrated_linear_weight {H : ℝ → ℝ} (hH : Continuous H) :
    (∫ x in (0 : ℝ)..1, x^2*weight H x) =
      53325*weightedPrimitive 1 H 1 - 185220*weightedPrimitive 3 H 1 +
        72135*weightedPrimitive 5 H 1 + 59760*(∫ x in (0 : ℝ)..1, x^8*H x) := by
  have hp : (fun x : ℝ => x^2*weight H x) =
      (fun x => 373275*(x^6*weightedPrimitive 1 H x) -
        926100*(x^4*weightedPrimitive 3 H x) + 216405*(x^2*weightedPrimitive 5 H x)) := by
    funext x
    unfold weight
    ring
  rw [hp, integral_three_terms (by fun_prop) (by fun_prop) (by fun_prop)]
  have h1 := weighted_integral_identity 1 6 hH
  have h3 := weighted_integral_identity 3 4 hH
  have h5 := weighted_integral_identity 5 2 hH
  norm_num at h1 h3 h5
  linarith

lemma integrated_quadratic_weight {H : ℝ → ℝ} (hH : Continuous H) :
    (∫ x in (0 : ℝ)..1, 2*x*H x*weight H x) =
      boundary (weightedPrimitive 1 H 1) (weightedPrimitive 3 H 1)
        (weightedPrimitive 5 H 1) -
        627480*(∫ x in (0 : ℝ)..1, x^3*(weightedPrimitive 1 H x)^2) := by
  have hp : (fun x : ℝ => 2*x*H x*weight H x) =
      (fun x => 746550*(x^5*H x*weightedPrimitive 1 H x) -
        1852200*(x^3*H x*weightedPrimitive 3 H x) +
        432810*(x*H x*weightedPrimitive 5 H x)) := by
    funext x
    unfold weight
    ring
  rw [hp, integral_three_terms (by fun_prop) (by fun_prop) (by fun_prop)]
  have hc := cross_primitive_identity 1 5 hH
  have hs := square_primitive_identity 3 hH
  have hw := weighted_square_identity hH
  simp only [pow_one] at hc
  unfold boundary
  linarith

end Rhone.Statistics.ThreeSiteSeparator
