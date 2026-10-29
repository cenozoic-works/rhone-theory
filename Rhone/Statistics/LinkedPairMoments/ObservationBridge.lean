/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.Kernel
public import Rhone.Statistics.PairObservationChannel.Observation

/-! # Panel law and panel weight as integrals of the conditional pair observation -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedPairMoments
open PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

theorem panel_weight_conditional (E : Channel K H) (k t : ℝ) (L : ℕ)
    (x : Fin L → H × H) :
    panelWeight E k t L x = ∏ i, conditionalMass E k t (x i).1 (x i).2 := by
  simp_rw [conditionalMass_eq_reportedMass]
  rfl

theorem panel_law_conditional (E : Channel K H) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    (L : ℕ) (x : Fin L → H × H) :
    (panelLaw E μ hk hμ L).mass x =
      ∫ t, ∏ i, conditionalMass E k t (x i).1 (x i).2 ∂μ := by
  change (∫ t, panelWeight E k t L x ∂μ) = _
  simp_rw [panel_weight_conditional]

end Rhone.Statistics.LinkedPairMoments
