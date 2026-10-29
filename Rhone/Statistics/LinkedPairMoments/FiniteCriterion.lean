/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.Features
public import Rhone.Statistics.LinkedPairMoments.Expansion

/-! # Exact finite-length criterion, including L=0 and k=0 -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.LinkedPairMoments
open DependenceBudget PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

theorem panel_eq_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) :
    panelLaw E μ hk hμ L = panelLaw E ν hk hν L ↔
      ∀ r : ℕ, r ≤ L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k) := by
  classical
  constructor
  · intro he r hr
    obtain ⟨S, _, hcard⟩ := Finset.exists_subset_card_eq
      (show r ≤ (Finset.univ : Finset (Fin L)).card by simpa using hr)
    have hs := congrArg (fun P => rejection P (panelStatistic E S)) he
    rw [panel_statistic_mean, panel_statistic_mean, hcard] at hs
    exact mul_left_cancel₀ (pow_ne_zero r ((retained_variance_pos_iff E).mpr hE).ne') hs
  · exact panel_eq_of_moments E μ ν hk hμ hν L

theorem panel_erased (E : Channel K H) (hE : retainedVariance E = 0) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) :
    panelLaw E μ hk hμ L = panelLaw E ν hk hν L := by
  apply finite_law_ext
  intro x
  change (∫ t, panelWeight E k t L x ∂μ) = ∫ t, panelWeight E k t L x ∂ν
  simp_rw [panelWeight, erased_mass E hE]
  simp

theorem panel_ne_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) :
    panelLaw E μ hk hμ L ≠ panelLaw E ν hk hν L ↔
      ∃ r : ℕ, r ≤ L ∧ pairLaplace μ ((r : ℝ) * k) ≠ pairLaplace ν ((r : ℝ) * k) := by
  rw [ne_eq, panel_eq_iff E hE μ ν hk hμ hν]
  push Not
  rfl

theorem next_moment_upgrade (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ)
    (hm : ∀ r : ℕ, r ≤ L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k))
    (hnext : pairLaplace μ (((L + 1 : ℕ) : ℝ) * k) ≠
      pairLaplace ν (((L + 1 : ℕ) : ℝ) * k)) :
    panelLaw E μ hk hμ L = panelLaw E ν hk hν L ∧
      panelLaw E μ hk hμ (L + 1) ≠ panelLaw E ν hk hν (L + 1) := by
  exact ⟨panel_eq_of_moments E μ ν hk hμ hν L hm,
    (panel_ne_iff E hE μ ν hk hμ hν (L + 1)).mpr ⟨L + 1, le_rfl, hnext⟩⟩

end Rhone.Statistics.LinkedPairMoments
