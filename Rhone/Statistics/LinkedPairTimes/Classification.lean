/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.FiniteCriterion

/-! # Two-linked-site criterion and zero-clock boundary -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.LinkedPairTimes
open PairObservationChannel LinkedPairMoments
variable {K : ℕ} {H : Type*} [Fintype H]

theorem two_site_eq_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    panelLaw E μ hk hμ 2 = panelLaw E ν hk hν 2 ↔
      pairLaplace μ k = pairLaplace ν k ∧ pairLaplace μ (2 * k) = pairLaplace ν (2 * k) := by
  rw [panel_eq_iff E hE μ ν hk hμ hν]
  constructor
  · intro h
    exact ⟨by simpa using h 1 (by omega), by simpa using h 2 (by omega)⟩
  · rintro ⟨h1, h2⟩ r hr
    interval_cases r
    · simp [pairLaplace]
    · simpa using h1
    · simpa using h2

theorem zero_clock_all_panels (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) :
    panelLaw E μ (by norm_num : (0 : ℝ) ≤ 0) hμ L =
      panelLaw E ν (by norm_num : (0 : ℝ) ≤ 0) hν L := by
  apply panel_eq_of_moments
  intro r _
  simp [pairLaplace]

theorem erased_two_sites (E : Channel K H) (hE : retainedVariance E = 0)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    panelLaw E μ hk hμ 2 = panelLaw E ν hk hν 2 := panel_erased E hE μ ν hk hμ hν 2

end Rhone.Statistics.LinkedPairTimes
