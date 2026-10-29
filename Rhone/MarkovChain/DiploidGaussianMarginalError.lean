/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianLifecycle
/-! # Multilocus Gaussian marginal viability bounds under the full homolog trait law -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory GaussianHouseOfCards
theorem diploidGaussianViability_marginal_error (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hab : Integrable (fun b => |haploidTrait n b|) μ)
    (hb2 : Integrable (fun b => (haploidTrait n b) ^ 2) μ) (a : Fin n → ℝ) :
    |(Probability.DiploidMarginalSelection.marginalViability μ (diploidGaussianViability n S)
        a).toReal -
      gaussianFitness S (haploidTrait n a)| ≤
    (|haploidTrait n a| * (∫ b, |haploidTrait n b| ∂μ) +
      (∫ b, (haploidTrait n b) ^ 2 ∂μ)/2)/S := by
  have ht := haploidTrait_measurable n
  have : IsProbabilityMeasure (μ.map (haploidTrait n)) :=
    (Measure.isProbabilityMeasure_map_iff ht.aemeasurable).mpr inferInstance
  have hAbs : Measurable (fun b : ℝ => |b|) := by fun_prop
  have hSq : Measurable (fun b : ℝ => b^2) := by fun_prop
  have hab' : Integrable (fun b : ℝ => |b|) (μ.map (haploidTrait n)) :=
    (integrable_map_measure (hAbs.aestronglyMeasurable) ht.aemeasurable).mpr hab
  have hb2' : Integrable (fun b : ℝ => b^2) (μ.map (haploidTrait n)) :=
    (integrable_map_measure (hSq.aestronglyMeasurable)
      ht.aemeasurable).mpr hb2
  rw [diploidGaussianViability_marginal n S hS μ a]
  have he := marginalGaussianFitness_error S hS (μ.map (haploidTrait n)) hab' hb2'
    (haploidTrait n a)
  rwa [integral_map ht.aemeasurable hAbs.aestronglyMeasurable,
    integral_map ht.aemeasurable hSq.aestronglyMeasurable] at he
end Rhone.MarkovChain.DiploidMarginalSelection
