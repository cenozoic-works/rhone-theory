/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianGameteIntegrability
/-! # Exact mutation moment balances for the full selected-parent and Mendelian lifecycle -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory
open scoped ENNReal NNReal

theorem diploidGaussianLifecycleUpdate_integrable_sq (n : ℕ) (S : ℝ) (hS : 0 < S)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (i : Fin n) :
    Integrable (fun a => (a i) ^ 2) (diploidGaussianLifecycleUpdate n S u T μ) := by
  have := diploidGaussian_gamete_probability n S hS μ
  exact gaussianIncrementMutation_integrable_sq n u T hu _
    (diploidGaussianGamete_integrable_sq n S hS μ h2) i

theorem diploidGaussianLifecycleUpdate_mean (n : ℕ) (S : ℝ) (hS : 0 < S)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (i : Fin n) :
    (∫ a, a i ∂diploidGaussianLifecycleUpdate n S u T μ) =
      ∫ a, a i ∂Probability.DiploidMarginalSelection.mendelianGameteLaw n μ
          (diploidGaussianViability n S) := by
  have := diploidGaussian_gamete_probability n S hS μ
  exact gaussianIncrementMutation_mean n u T hu _
    (diploidGaussianGamete_integrable_sq n S hS μ h2) i

theorem diploidGaussianLifecycleUpdate_second (n : ℕ) (S : ℝ) (hS : 0 < S)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (i : Fin n) :
    (∫ a, (a i) ^ 2 ∂diploidGaussianLifecycleUpdate n S u T μ) =
      (∫ a, (a i) ^ 2 ∂Probability.DiploidMarginalSelection.mendelianGameteLaw n μ
          (diploidGaussianViability n S))+
        u i*(T i : ℝ) := by
  have := diploidGaussian_gamete_probability n S hS μ
  exact gaussianIncrementMutation_second n u T hu _
    (diploidGaussianGamete_integrable_sq n S hS μ h2) i

theorem diploidGaussianLifecycleUpdate_cross (n : ℕ) (S : ℝ) (hS : 0 < S)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ a, a i*a j ∂diploidGaussianLifecycleUpdate n S u T μ) =
      ∫ a, a i*a j ∂Probability.DiploidMarginalSelection.mendelianGameteLaw n μ
          (diploidGaussianViability n S) := by
  have := diploidGaussian_gamete_probability n S hS μ
  exact gaussianIncrementMutation_cross n u T hu _
    (diploidGaussianGamete_integrable_sq n S hS μ h2) i j hij

end Rhone.MarkovChain.DiploidMarginalSelection
