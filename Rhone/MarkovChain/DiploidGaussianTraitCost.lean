/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianLifecycle
public import Rhone.MarkovChain.DiploidGaussianRelativeCost
/-! # Relative marginal viability cost derived from the symmetric haplotype law -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem haploidTraitLaw_reflection (n : ℕ) (μ : Measure (Fin n → ℝ))
    (hsym : μ.map (fun a => -a) = μ) :
    (μ.map (haploidTrait n)).map (fun b => -b) = μ.map (haploidTrait n) := by
  rw [Measure.map_map measurable_neg (haploidTrait_measurable n)]
  have he : (fun b : ℝ => -b) ∘ haploidTrait n =
      haploidTrait n ∘ (fun a => -a) := by
    funext a
    simp [haploidTrait]
  rw [he, ← Measure.map_map (haploidTrait_measurable n) (by fun_prop), hsym]

theorem haploidTraitLaw_integrable_sq (n : ℕ) (μ : Measure (Fin n → ℝ))
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) :
    Integrable (fun b : ℝ => b ^ 2) (μ.map (haploidTrait n)) := by
  have hm (i : Fin n) : MemLp (fun a => a i) 2 μ :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable).mpr (h2 i)
  have ht : MemLp (haploidTrait n) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hm i)
  exact (integrable_map_measure (by fun_prop)
    (haploidTrait_measurable n).aemeasurable).mpr ht.integrable_sq

theorem diploidGaussianViability_relative_cost_error (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun a => -a) = μ)
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (a : Fin n → ℝ)
    (ha0 : 0 < (haploidTrait n a) ^ 2) (haS : (haploidTrait n a) ^ 2 ≤ 2 * S) :
    |(1-(Probability.DiploidMarginalSelection.marginalViability μ (diploidGaussianViability n S)
        a).toReal/
        (Probability.DiploidMarginalSelection.marginalViability μ (diploidGaussianViability n S)
            0).toReal)/
        (1-GaussianHouseOfCards.gaussianFitness S (haploidTrait n a))-1| ≤
      2*(∫ b, (haploidTrait n b) ^ 2 ∂μ)/
        (S*(Probability.DiploidMarginalSelection.marginalViability μ (diploidGaussianViability n S)
            0).toReal) := by
  have := (Measure.isProbabilityMeasure_map_iff
    (haploidTrait_measurable n).aemeasurable).mpr (inferInstance : IsProbabilityMeasure μ)
  have hb := marginalGaussianSelectionCost_relative_error S hS (μ.map (haploidTrait n))
    (haploidTraitLaw_reflection n μ hsym) (haploidTraitLaw_integrable_sq n μ h2)
    (haploidTrait n a) ha0 haS
  rw [diploidGaussianViability_marginal n S hS μ a,
    diploidGaussianViability_marginal n S hS μ 0]
  have hz : haploidTrait n 0 = 0 := by simp [haploidTrait]
  rw [hz]
  rw [integral_map (haploidTrait_measurable n).aemeasurable (by fun_prop)] at hb
  exact hb
end Rhone.MarkovChain.DiploidMarginalSelection
