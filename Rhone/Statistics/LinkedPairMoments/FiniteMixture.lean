/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.FiniteProduct
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Finite-alphabet mixtures for linked-panel measures -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedPairMoments
open DependenceBudget DependentPairedTest
variable {T X : Type*} [MeasurableSpace T] [Fintype X]

noncomputable def finiteMixture (μ : Measure T) [IsProbabilityMeasure μ]
    (w : T → X → ℝ) (hi : ∀ x, Integrable (fun t => w t x) μ)
    (hn : ∀ x, ∀ᵐ t ∂μ, 0 ≤ w t x) (ht : ∀ᵐ t ∂μ, ∑ x, w t x = 1) : Law X where
  mass := fun x => ∫ t, w t x ∂μ
  nonneg := fun x => integral_nonneg_of_ae (hn x)
  total := by
    rw [← integral_finsetSum _ (fun x _ => hi x)]
    rw [integral_congr_ae ht]
    simp

theorem finite_mixture_expectation (μ : Measure T) [IsProbabilityMeasure μ]
    (w : T → X → ℝ) (hi : ∀ x, Integrable (fun t => w t x) μ)
    (hn : ∀ x, ∀ᵐ t ∂μ, 0 ≤ w t x) (ht : ∀ᵐ t ∂μ, ∑ x, w t x = 1)
    (f : X → ℝ) :
    rejection (finiteMixture μ w hi hn ht) f = ∫ t, ∑ x, w t x * f x ∂μ := by
  unfold rejection finiteMixture
  simp_rw [← integral_mul_const]
  exact (integral_finsetSum _ (fun x _ => (hi x).mul_const (f x))).symm

end Rhone.Statistics.LinkedPairMoments
