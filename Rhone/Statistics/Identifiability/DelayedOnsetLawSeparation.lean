/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DelayedOnsetRestart
public import Rhone.Statistics.Identifiability.TimeVaryingIntegrablePanSeparation

/-! # Conditional full-law endpoints for continuous delayed-onset island histories -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.DelayedOnset
open SimultaneousOnset

theorem jointLaw_ne_pan_of_witness_after (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a)
    (hw : ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → 0 < SimultaneousOnset.witness k c q r (a + t))
    (hC : ∀ δ : ℝ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw := by
  obtain ⟨δ, hδ, hpos⟩ := hw
  obtain ⟨t, ht, htδ, hct⟩ := hC δ hδ
  exact timeVaryingJointLaw_ne_integrable_pan_of_positive_witness k c q r hc hq hr
    hcn hqn hrn hpair (add_pos_of_nonneg_of_pos ha ht) hct (hpos t ht htδ) P

theorem jointLaw_ne_pan_after_recombination_prefix (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hy : 0 < y)
    (hprefix : (fun i : ProductState => preRow k c q r a i.1 * pairRow k c q a i.2) =
      recombinationPrefixRow x y)
    (hR : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, r (a + u))
    (hC : ∀ δ : ℝ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw := by
  obtain ⟨δ, hδ, hpos⟩ := witness_positive_after_recombination_prefix k c q r
    hc hq hr hcn hqn hrn ha hx hy hprefix
  exact jointLaw_ne_pan_of_witness_after k c q r hc hq hr hcn hqn hrn hpair ha
    ⟨δ, hδ, fun t ht htδ => hpos t ht htδ (hR t ht)⟩ hC P

theorem jointLaw_ne_pan_after_migration_prefix (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {a b S : ℝ} (ha : 0 ≤ a) (x z : ℝ) (hb : 0 < b) (hS : 0 < S)
    (hprefix : (fun i : ProductState => preRow k c q r a i.1 * pairRow k c q a i.2) =
      migrationPrefixRow x b z S)
    (hQ : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, q (a + u))
    (hC : ∀ δ : ℝ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw := by
  obtain ⟨δ, hδ, hpos⟩ := witness_positive_after_migration_prefix k c q r
    hc hq hr hcn hqn hrn ha x z hb hS hprefix
  exact jointLaw_ne_pan_of_witness_after k c q r hc hq hr hcn hqn hrn hpair ha
    ⟨δ, hδ, fun t ht htδ => hpos t ht htδ (hQ t ht)⟩ hC P

end Rhone.Statistics.Identifiability.DelayedOnset
