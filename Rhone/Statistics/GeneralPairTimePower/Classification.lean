/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.GeneralPairTimePower.PooledWitness
public import Rhone.Statistics.DependentPairedTest.MeasureBridge
public import Rhone.Statistics.LinkedAgreementPower.BinaryTesting

/-! # One-common-proper-pan classification and fixed-witness iid equality -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.GeneralPairTimePower
open DependenceBudget PairObservationChannel DependentPairedTest
open LinkedAgreementPower Identifiability.FinitePanelSampling
variable {K : ℕ} {H : Type*} [Fintype H]

theorem proper_pan_match_iff (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 < t) (hν : ∀ᵐ t ∂ν, 0 < t) :
    (∃ r : ℝ → ℝ, ∃ hr : AdmittedPan r, ∃ κ : ℝ, ∃ hκ : 0 ≤ κ,
      observedLaw E μ hk.le (hμ.mono fun _ h => h.le) = panObservedLaw E r hr hκ ∧
      observedLaw E ν hk.le (hν.mono fun _ h => h.le) = panObservedLaw E r hr hκ) ↔
      pairLaplace μ k = pairLaplace ν k ∨ retainedVariance E = 0 := by
  constructor
  · rintro ⟨r, hr, κ, hκ, he1, he2⟩
    exact (reported_pair_eq_iff E μ ν hk.le (hμ.mono fun _ h => h.le)
      (hν.mono fun _ h => h.le)).mp (he1.trans he2.symm)
  · intro h
    have he := (reported_pair_eq_iff E μ ν hk.le (hμ.mono fun _ h => h.le)
      (hν.mono fun _ h => h.le)).mpr h
    refine ⟨fun _ => matchingRate k (pairLaplace μ k),
      constant_pan_admitted (matching_rate_pos hk (laplace_strict_interval μ hk hμ)), k, hk.le,
      (matching_observed_law E μ hk hμ).symm, ?_⟩
    exact he.symm.trans (matching_observed_law E μ hk hμ).symm

theorem exact_iid_pan_match_when [MeasurableSpace H] [MeasurableSingletonClass H]
    (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 < t) (hν : ∀ᵐ t ∂ν, 0 < t)
    (hmatch : pairLaplace μ k = pairLaplace ν k ∨ retainedVariance E = 0) :
    ∃ r : ℝ → ℝ, ∃ hr : AdmittedPan r, ∀ N : ℕ,
      iidLaw (lawMeasure (independentPair
        (observedLaw E μ hk.le (hμ.mono fun _ h => h.le))
        (observedLaw E ν hk.le (hν.mono fun _ h => h.le)))) N =
      iidLaw (lawMeasure (independentPair (panObservedLaw E r hr hk.le)
        (panObservedLaw E r hr hk.le))) N := by
  have he := (reported_pair_eq_iff E μ ν hk.le (hμ.mono fun _ h => h.le)
    (hν.mono fun _ h => h.le)).mpr hmatch
  refine ⟨fun _ => matchingRate k (pairLaplace μ k),
    constant_pan_admitted (matching_rate_pos hk (laplace_strict_interval μ hk hμ)), ?_⟩
  intro N
  rw [matching_observed_law E μ hk hμ, ← he]

end Rhone.Statistics.GeneralPairTimePower
