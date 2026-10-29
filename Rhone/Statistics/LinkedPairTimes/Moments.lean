/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedAgreementPower.Feature
public import Rhone.Statistics.LinkedPairTimes.Classification

/-! # Exact two-site all-agreement expectation -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedPairTimes
open DependenceBudget PairObservationChannel LinkedPairMoments
open LinkedAgreementPower
variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem two_agreement_mean (E : Channel K H) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) :
    rejection (panelLaw E μ hk hμ 2) allAgreement =
      baseline E ^ 2 + 2 * baseline E * retainedVariance E * pairLaplace μ k +
        retainedVariance E ^ 2 * pairLaplace μ (2 * k) := by
  rw [all_agreement_mean_expansion]
  have hs : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hs]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [pairLaplace, Fin.ext_iff]
  ring

end Rhone.Statistics.LinkedPairTimes
