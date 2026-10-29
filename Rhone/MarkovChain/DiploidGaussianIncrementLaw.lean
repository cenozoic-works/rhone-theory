/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianMeiosis
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Integration

/-! # Independent Gaussian mutation increments on the full haplotype law -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable def locusIncrementLaw (u : ℝ) (T : ℝ≥0) : Measure ℝ :=
  ENNReal.ofReal (1-u) • Measure.dirac 0 + ENNReal.ofReal u • gaussianReal 0 T

noncomputable def mutationIncrementLaw (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => locusIncrementLaw (u i) (T i))

noncomputable def gaussianIncrementMutation (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (μ : Measure (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  (μ.prod (mutationIncrementLaw n u T)).map (fun p => fun i => p.1 i+p.2 i)

noncomputable def diploidGaussianLifecycleUpdate (n : ℕ) (S : ℝ)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0)
    (μ : Measure (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  gaussianIncrementMutation n u T
    (Probability.DiploidMarginalSelection.mendelianGameteLaw n μ (diploidGaussianViability n S))

theorem locusIncrementLaw_probability (u : ℝ) (T : ℝ≥0) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    IsProbabilityMeasure (locusIncrementLaw u T) := by
  constructor
  simp only [locusIncrementLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hu0]
  norm_num

theorem mutationIncrementLaw_probability (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    IsProbabilityMeasure (mutationIncrementLaw n u T) := by
  have (i : Fin n) : IsProbabilityMeasure (locusIncrementLaw (u i) (T i)) :=
    locusIncrementLaw_probability _ _ (hu i).1 (hu i).2
  unfold mutationIncrementLaw
  infer_instance

theorem gaussianIncrementMutation_probability (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (gaussianIncrementMutation n u T μ) := by
  have := mutationIncrementLaw_probability n u T hu
  unfold gaussianIncrementMutation
  apply (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr
  infer_instance

theorem diploidGaussianLifecycleUpdate_probability (n : ℕ) (S : ℝ) (hS : 0 < S)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (diploidGaussianLifecycleUpdate n S u T μ) := by
  have := diploidGaussian_gamete_probability n S hS μ
  exact gaussianIncrementMutation_probability n u T hu _

end Rhone.MarkovChain.DiploidMarginalSelection
