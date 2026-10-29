/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedAgreementPower.Feature

/-! # Cancellation at the first differing Laplace moment -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedAgreementPower
open DependenceBudget PairObservationChannel LinkedPairMoments
variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem first_difference_gap (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ)
    (hm : ∀ r : ℕ, r < L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k)) :
    rejection (panelLaw E μ hk hμ L) allAgreement -
      rejection (panelLaw E ν hk hν L) allAgreement =
    retainedVariance E ^ L * (pairLaplace μ ((L : ℝ) * k) - pairLaplace ν ((L : ℝ) * k)) := by
  rw [all_agreement_mean_expansion, all_agreement_mean_expansion, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin L))]
  · simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, mul_one]
    ring1
  · intro S _ hS
    have hlt : S.card < L := by
      simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS)
    rw [hm S.card hlt, sub_self]
  · simp

theorem first_agreement_mean_ne (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ)
    (hm : ∀ r : ℕ, r < L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k))
    (hL : pairLaplace μ ((L : ℝ) * k) ≠ pairLaplace ν ((L : ℝ) * k)) :
    rejection (panelLaw E μ hk hμ L) allAgreement ≠
      rejection (panelLaw E ν hk hν L) allAgreement := by
  apply sub_ne_zero.mp
  rw [first_difference_gap E μ ν hk hμ hν L hm]
  exact mul_ne_zero (pow_ne_zero L ((retained_variance_pos_iff E).mpr hE).ne')
    (sub_ne_zero.mpr hL)

theorem exists_first_moment (μ ν : Measure ℝ) (k : ℝ)
    (h : ∃ n : ℕ, pairLaplace μ ((n : ℝ) * k) ≠ pairLaplace ν ((n : ℝ) * k)) :
    ∃ L : ℕ, (pairLaplace μ ((L : ℝ) * k) ≠ pairLaplace ν ((L : ℝ) * k)) ∧
      ∀ r : ℕ, r < L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k) := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro r hr
  exact not_ne_iff.mp (Nat.find_min h hr)

end Rhone.Statistics.LinkedAgreementPower
