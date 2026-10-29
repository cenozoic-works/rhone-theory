/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DelayedPrefixMasses
public import Rhone.Statistics.Identifiability.DelayedOnsetLawSeparation

/-! # Unconditional rate-history endpoints for the two strictly ordered onset cases -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.DelayedOnset
open SimultaneousOnset

theorem jointLaw_ne_pan_of_delayed_recombination (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a) (hbefore : ∀ u ∈ Icc 0 a, r u = 0)
    (hQ : 0 < ∫ u in (0 : ℝ)..a, q u)
    (hR : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, r (a + u))
    (hC : ∀ δ : ℝ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw :=
  jointLaw_ne_pan_after_recombination_prefix k c q r hc hq hr hcn hqn hrn hpair ha
    (pairRow_together_positive k c q hc hq hqn ha)
    (pairRow_apart_positive k c q hc hq hqn ha hQ)
    (recombination_prefix_of_zero_history k c q r hc hq hr ha hbefore) hR hC P

theorem jointLaw_ne_pan_of_delayed_migration (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a) (hbefore : ∀ u ∈ Icc 0 a, q u = 0)
    (hR : 0 < ∫ u in (0 : ℝ)..a, r u)
    (hQ : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, q (a + u))
    (hC : ∀ δ : ℝ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw :=
  jointLaw_ne_pan_after_migration_prefix k c q r hc hq hr hcn hqn hrn hpair ha
    (preRow k c q r a 0) (preRow k c q r a 7)
    (preRow_recombined_positive k c q r hc hq hr hcn hqn hrn ha hR)
    (pairRow_together_positive k c q hc hq hqn ha)
    (migration_prefix_of_zero_history k c q r hc hq hr ha hbefore) hQ hC P

end Rhone.Statistics.Identifiability.DelayedOnset
