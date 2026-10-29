/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeAlleleIntegerIdentification

/-! # Integer-clock uniqueness endpoint for linked-pair moments -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.LinkedPairMoments

noncomputable def laplace (μ : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ t, Real.exp (-s*t) ∂μ

theorem all_laplace_moments_injective (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (he : ∀ n : ℕ, laplace μ ((n : ℝ)*k) = laplace ν ((n : ℝ)*k)) : μ = ν := by
  apply Identifiability.ThreeAlleleMutation.nonnegative_laplace_unique_positive_grid
    μ ν hk hμ hν
  intro n _
  simpa [laplace, mul_comm k] using he n

theorem all_laplace_moments_eq_iff (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    (∀ n : ℕ, laplace μ ((n : ℝ)*k) = laplace ν ((n : ℝ)*k)) ↔ μ = ν := by
  constructor
  · exact all_laplace_moments_injective μ ν hk hμ hν
  · rintro rfl n
    rfl

end Rhone.Statistics.LinkedPairMoments
