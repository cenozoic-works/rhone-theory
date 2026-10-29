/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.WeightedPrimitive
public import Rhone.Statistics.ThreeSiteSeparator.Score

/-! # Pointwise algebra for the exact cubic CDF functional -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

def weight (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  373275*x^4*weightedPrimitive 1 F x - 926100*x^2*weightedPrimitive 3 F x +
    216405*weightedPrimitive 5 F x

@[fun_prop]
lemma weight_continuous {F : ℝ → ℝ} (hF : Continuous F) : Continuous (weight F) := by
  unfold weight
  fun_prop

lemma weight_centered {F : ℝ → ℝ} (hF : Continuous F) (x : ℝ) :
    weight F x = weight (fun t => F t - t) x - 29880*x^7 := by
  unfold weight
  rw [weightedPrimitive_centered 1 hF, weightedPrimitive_centered 3 hF,
    weightedPrimitive_centered 5 hF]
  norm_num
  ring

lemma cubic_integrand_centered {F : ℝ → ℝ} (hF : Continuous F) (x : ℝ) :
    (F x)^2 * weight F x =
      -29880*x^9 - 59760*x^8*(F x - x) +
        x^2*weight (fun t => F t - t) x +
        2*x*(F x - x)*weight (fun t => F t - t) x +
        (F x - x)^2*weight F x := by
  rw [weight_centered hF x]
  ring

def cdfFunctional (F : ℝ → ℝ) : ℝ :=
  -6360 - 53325*weightedPrimitive 1 F 1 + 185220*weightedPrimitive 3 F 1 -
    72135*weightedPrimitive 5 F 1 + ∫ x in (0 : ℝ)..1, (F x)^2*weight F x

lemma functional_centered_constants {F : ℝ → ℝ} (hF : Continuous F) :
    cdfFunctional F =
      2604 - 53325*weightedPrimitive 1 (fun t => F t - t) 1 +
        185220*weightedPrimitive 3 (fun t => F t - t) 1 -
        72135*weightedPrimitive 5 (fun t => F t - t) 1 +
        ∫ x in (0 : ℝ)..1, (F x)^2*weight F x := by
  unfold cdfFunctional
  rw [weightedPrimitive_centered 1 hF, weightedPrimitive_centered 3 hF,
    weightedPrimitive_centered 5 hF]
  norm_num
  ring

end Rhone.Statistics.ThreeSiteSeparator
