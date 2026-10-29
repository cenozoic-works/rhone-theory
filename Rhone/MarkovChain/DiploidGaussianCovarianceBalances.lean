/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianLifecycleBalances
public import Mathlib.Probability.Moments.Covariance
/-! # Centred coordinate balances for the selected Mendelian diploid lifecycle -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem diploidGaussianLifecycleUpdate_covariance (n : ℕ) (S : ℝ) (hS : 0 < S)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ)
    (i j : Fin n) (hij : i ≠ j) :
    ProbabilityTheory.covariance (fun a => a i) (fun a => a j)
      (diploidGaussianLifecycleUpdate n S u T μ) =
    ProbabilityTheory.covariance (fun a => a i) (fun a => a j)
      (Probability.DiploidMarginalSelection.mendelianGameteLaw n μ
          (diploidGaussianViability n S)) := by
  have := diploidGaussian_gamete_probability n S hS μ
  have := diploidGaussianLifecycleUpdate_probability n S hS u T hu μ
  have hg (k : Fin n) : MemLp (fun a => a k) 2
      (Probability.DiploidMarginalSelection.mendelianGameteLaw n μ
          (diploidGaussianViability n S)) :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply k).aestronglyMeasurable).mpr
      (diploidGaussianGamete_integrable_sq n S hS μ h2 k)
  have hn (k : Fin n) : MemLp (fun a => a k) 2
      (diploidGaussianLifecycleUpdate n S u T μ) :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply k).aestronglyMeasurable).mpr
      (diploidGaussianLifecycleUpdate_integrable_sq n S hS u T hu μ h2 k)
  rw [covariance_eq_sub (hn i) (hn j), covariance_eq_sub (hg i) (hg j)]
  change (∫ a, a i*a j ∂diploidGaussianLifecycleUpdate n S u T μ) - _ = _
  rw [diploidGaussianLifecycleUpdate_cross n S hS u T hu μ h2 i j hij,
    diploidGaussianLifecycleUpdate_mean n S hS u T hu μ h2 i,
    diploidGaussianLifecycleUpdate_mean n S hS u T hu μ h2 j]
  rfl

theorem diploidGaussianLifecycleUpdate_diagonal_covariance (n : ℕ) (S : ℝ) (hS : 0 < S)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ)
    (i : Fin n) :
    ProbabilityTheory.covariance (fun a => a i) (fun a => a i)
      (diploidGaussianLifecycleUpdate n S u T μ) =
    ProbabilityTheory.covariance (fun a => a i) (fun a => a i)
      (Probability.DiploidMarginalSelection.mendelianGameteLaw n μ (diploidGaussianViability n S)) +
          u i*(T i : ℝ) := by
  have := diploidGaussian_gamete_probability n S hS μ
  have := diploidGaussianLifecycleUpdate_probability n S hS u T hu μ
  have hg (k : Fin n) : MemLp (fun a => a k) 2
      (Probability.DiploidMarginalSelection.mendelianGameteLaw n μ
          (diploidGaussianViability n S)) :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply k).aestronglyMeasurable).mpr
      (diploidGaussianGamete_integrable_sq n S hS μ h2 k)
  have hn (k : Fin n) : MemLp (fun a => a k) 2
      (diploidGaussianLifecycleUpdate n S u T μ) :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply k).aestronglyMeasurable).mpr
      (diploidGaussianLifecycleUpdate_integrable_sq n S hS u T hu μ h2 k)
  rw [covariance_eq_sub (hn i) (hn i), covariance_eq_sub (hg i) (hg i)]
  simp only [Pi.mul_apply]
  simp_rw [← pow_two]
  rw [diploidGaussianLifecycleUpdate_second n S hS u T hu μ h2 i,
    diploidGaussianLifecycleUpdate_mean n S hS u T hu μ h2 i]
  ring

end Rhone.MarkovChain.DiploidMarginalSelection
