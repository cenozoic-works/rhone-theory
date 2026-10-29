/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.GeneralPairTimePower.Laplace
public import Rhone.Statistics.PairObservationChannel.Observation
public import Rhone.Statistics.LinkedPairMoments.Expansion

/-! # Full one-site observation law and exact equality criterion -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.GeneralPairTimePower
open DependenceBudget PairObservationChannel LinkedPairMoments
variable {K : ℕ} {H : Type*} [Fintype H]

def observedLaw (E : Channel K H) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) : Law (H × H) :=
  reportedLaw E (pairLaplace μ k) (pair_laplace_bounds μ hk hμ)

theorem observedLaw_mass (E : Channel K H) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (x y : H) :
    (observedLaw E μ hk hμ).mass (x, y) = observedMass E μ k x y :=
  (observed_mass_formula E μ hk hμ x y).symm

theorem reported_pair_eq_iff (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    observedLaw E μ hk hμ = observedLaw E ν hk hν ↔
      pairLaplace μ k = pairLaplace ν k ∨ retainedVariance E = 0 := by
  constructor
  · intro he
    apply (reported_mass_eq_iff E _ _).mp
    intro x y
    exact congrArg (fun P : Law (H × H) => P.mass (x, y)) he
  · intro he
    apply finite_law_ext
    intro x
    exact (reported_mass_eq_iff E _ _).mpr he x.1 x.2

theorem reported_pair_ne_iff (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    observedLaw E μ hk hμ ≠ observedLaw E ν hk hν ↔
      pairLaplace μ k ≠ pairLaplace ν k ∧ Informative E := by
  rw [ne_eq, reported_pair_eq_iff E μ ν hk hμ hν, not_or]
  have he : retainedVariance E ≠ 0 ↔ Informative E := by
    rw [← retained_variance_pos_iff]
    constructor
    · intro hn
      exact lt_of_le_of_ne (retained_variance_nonneg E) (Ne.symm hn)
    · intro hp
      exact hp.ne'
  exact and_congr_right (fun _ => he)

end Rhone.Statistics.GeneralPairTimePower
