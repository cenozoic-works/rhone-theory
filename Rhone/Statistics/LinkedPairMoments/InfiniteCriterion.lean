/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.FiniteCriterion
public import Rhone.Statistics.LinkedPairMoments.CompactClock

/-! # All-length equivalence at one fixed positive mutation clock -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.LinkedPairMoments
open PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

theorem all_panels_eq_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    (∀ L : ℕ, panelLaw E μ hk.le hμ L = panelLaw E ν hk.le hν L) ↔ μ = ν := by
  constructor
  · intro he
    apply all_laplace_moments_injective μ ν hk hμ hν
    intro r
    exact (panel_eq_iff E hE μ ν hk.le hμ hν r).mp (he r) r le_rfl
  · rintro rfl L
    rfl

theorem some_panel_separates_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    (∃ L : ℕ, panelLaw E μ hk.le hμ L ≠ panelLaw E ν hk.le hν L) ↔ μ ≠ ν := by
  have h := (all_panels_eq_iff E hE μ ν hk hμ hν).not
  push Not at h
  exact h

end Rhone.Statistics.LinkedPairMoments
