/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FiniteBlockModel.OrderedCriterion
public import Rhone.Statistics.Identifiability.ThreeSamplingSurvivalProfile

/-! # Symmetric-island endpoint -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators
namespace Rhone.Statistics.FiniteBlockModel
open WeakRegularSeparation Algebra.Identifiability MarkovChain.Identifiability Identifiability
    ThreeSampleMembership

theorem island_uniformlySeparated_iff (ρ : ThreeSampling.State → ℝ) (n : ℕ)
    (c q : ℝ → ℝ) [IsProbabilityMeasure (ThreeSampling.law ρ n c q)]
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (_hadmissible : n = 0 → ρ 2 = 0)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    {k : ℝ} (hk : 0 < k) :
    UniformlySeparated k (uniformLift (ThreeSampling.durationLaw ρ n c q)) ↔
      ¬(ρ = Pi.single 0 1 ∧ (∀ᵐ t, 0 ≤ t → q t = 0) ∧
        Tendsto (integrablePanClock c) atTop atTop) := by
  change UniformlySeparated k (uniformLift (durations (ThreeSampling.law ρ n c q))) ↔ _
  rw [ordered_uniformlySeparated_iff hk _ (ThreeSampling.law_ordered_support ρ n c q)
    (ThreeSampling.sourceProfile ρ n c q hρ hρsum hc hq hcn hqn)
    (ThreeSampling.sourceProfile_matches ρ n c q hρ hρsum hc hq hcn hqn)]
  exact not_congr (ThreeSampling.Unrestricted.pan_representable_iff
    ρ n c q hρ hρsum hc hq hcn hqn)

end Rhone.Statistics.FiniteBlockModel
