/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.EnergySign

/-! # CDF moment formulas and their algebraic reduction to the signed energy -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

def cdfPairMoment (r : ℕ) (F : ℝ → ℝ) : ℝ :=
  1 - (r : ℝ)*weightedPrimitive (r - 1) F 1

def cdfMixedMoment (p q : ℕ) (F : ℝ → ℝ) : ℝ :=
  1 - (3*(q : ℝ)/2)*weightedPrimitive (q - 1) F 1 +
    ((q : ℝ)/2 - p)*(∫ x in (0 : ℝ)..1, x^(p + q - 1)*(F x)^3) +
    (3*(p : ℝ)*q/2)*(∫ x in (0 : ℝ)..1,
      x^(p - 1)*(F x)^2*weightedPrimitive (q - 1) F x)

def cdfH (F : ℝ → ℝ) : ℝ := (cdfMixedMoment 5 2 F + 2*cdfMixedMoment 1 6 F)/3

def cdfJ (F : ℝ → ℝ) : ℝ := (2*cdfMixedMoment 3 4 F + cdfMixedMoment 1 6 F)/3

lemma functional_moment_reduction {F : ℝ → ℝ} (hF : Continuous F) :
    15*linearScore (cdfPairMoment 2 F) (cdfPairMoment 4 F) (cdfPairMoment 6 F)
      (cdfH F) (cdfJ F) = cdfFunctional F := by
  have hp : (fun x : ℝ => (F x)^2*weight F x) =
      (fun x => 373275*(x^4*(F x)^2*weightedPrimitive 1 F x) -
        926100*(x^2*(F x)^2*weightedPrimitive 3 F x) +
        216405*((F x)^2*weightedPrimitive 5 F x)) := by
    funext x
    unfold weight
    ring
  unfold cdfFunctional
  rw [hp, integral_three_terms (by fun_prop) (by fun_prop) (by fun_prop)]
  unfold linearScore cdfPairMoment cdfH cdfJ cdfMixedMoment
  norm_num
  ring

lemma centered_pair_moments {F : ℝ → ℝ} (hF : Continuous F) :
    -(cdfPairMoment 2 F - 1 / 3)/2 = weightedPrimitive 1 (fun t => F t - t) 1 ∧
    -(cdfPairMoment 4 F - 1 / 5)/4 = weightedPrimitive 3 (fun t => F t - t) 1 ∧
    -(cdfPairMoment 6 F - 1 / 7)/6 = weightedPrimitive 5 (fun t => F t - t) 1 := by
  unfold cdfPairMoment
  norm_num
  rw [weightedPrimitive_centered 1 hF, weightedPrimitive_centered 3 hF,
    weightedPrimitive_centered 5 hF]
  norm_num
  constructor
  · ring
  constructor <;> ring

theorem cdf_moment_score_nonpos (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, 0 ≤ z) {F : ℝ → ℝ} (hF : Continuous F)
    (he : ∀ x, F x = μ.real (Iic x)) :
    score (cdfPairMoment 2 F) (cdfPairMoment 4 F) (cdfPairMoment 6 F) (cdfH F) (cdfJ F) ≤ 0 := by
  apply score_nonpos_of_energy
  rw [functional_moment_reduction hF]
  obtain ⟨h1, h3, h5⟩ := centered_pair_moments hF
  rw [h1, h3, h5]
  exact cdf_functional_bound μ hμ hF he

end Rhone.Statistics.ThreeSiteSeparator
