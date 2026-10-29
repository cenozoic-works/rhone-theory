/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedAgreementPower.FirstMoment
public import Rhone.Statistics.LinkedAgreementPower.BinaryTesting
public import Rhone.Statistics.LinkedPairMoments.InfiniteCriterion

/-! # First-informative-panel testing classification -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.LinkedAgreementPower
open DependenceBudget PairObservationChannel LinkedPairMoments
variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem panel_test_common_size {L : ℕ} (P : Law (Fin L → H × H)) (N : ℕ) :
    independentTest P P allAgreement N ≤ (1 : ℝ) / 20 :=
  binary_test_common_size P (all_agreement_binary L) N

theorem first_panel_power_conservative (E : Channel K H) (_hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L N : ℕ)
    (hm : ∀ r : ℕ, r < L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k))
    (_hL : pairLaplace μ ((L : ℝ) * k) ≠ pairLaplace ν ((L : ℝ) * k))
    (hb : 160 ≤ N * (retainedVariance E ^ L *
      (pairLaplace μ ((L : ℝ) * k) - pairLaplace ν ((L : ℝ) * k))) ^ 2) :
    (19 : ℝ) / 20 ≤ independentTest (panelLaw E μ hk hμ L) (panelLaw E ν hk hν L)
      allAgreement N := by
  apply DependentPairedTest.coupling_worst_discordance_power
    _ _ _ (independent_coupling _ _) (all_agreement_binary L) (all_agreement_binary L) N
  rw [first_difference_gap E μ ν hk hμ hν L hm]
  exact hb

theorem first_panel_power (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L N : ℕ)
    (hm : ∀ r : ℕ, r < L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k))
    (hL : pairLaplace μ ((L : ℝ) * k) ≠ pairLaplace ν ((L : ℝ) * k))
    (hb : 160 *
      (rejection (panelLaw E μ hk hμ L) allAgreement +
        rejection (panelLaw E ν hk hν L) allAgreement -
        2 * rejection (panelLaw E μ hk hμ L) allAgreement *
          rejection (panelLaw E ν hk hν L) allAgreement) ≤
      N * (retainedVariance E ^ L *
        (pairLaplace μ ((L : ℝ) * k) - pairLaplace ν ((L : ℝ) * k))) ^ 2) :
    (19 : ℝ) / 20 ≤ independentTest (panelLaw E μ hk hμ L) (panelLaw E ν hk hν L)
      allAgreement N := by
  apply binary_signed_power _ _ (all_agreement_binary L) N
    (first_agreement_mean_ne E hE μ ν hk hμ hν L hm hL)
  rw [first_difference_gap E μ ν hk hμ hν L hm]
  exact hb

theorem some_agreement_test_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    (∃ L N : ℕ, (19 : ℝ) / 20 ≤
      independentTest (panelLaw E μ hk.le hμ L) (panelLaw E ν hk.le hν L) allAgreement N) ↔
      μ ≠ ν := by
  constructor
  · rintro ⟨L, N, hp⟩ rfl
    have hs := panel_test_common_size (panelLaw E μ hk.le hμ L) N
    linarith
  · intro hne
    have hex : ∃ n : ℕ, pairLaplace μ ((n : ℝ) * k) ≠ pairLaplace ν ((n : ℝ) * k) := by
      by_contra h
      push Not at h
      exact hne (all_laplace_moments_injective μ ν hk hμ hν h)
    obtain ⟨L, hL, hm⟩ := exists_first_moment μ ν k hex
    obtain ⟨N, hN⟩ := binary_test_exists (panelLaw E μ hk.le hμ L) (panelLaw E ν hk.le hν L)
      (all_agreement_binary L) (first_agreement_mean_ne E hE μ ν hk.le hμ hν L hm hL)
    exact ⟨L, N, hN⟩

end Rhone.Statistics.LinkedAgreementPower
