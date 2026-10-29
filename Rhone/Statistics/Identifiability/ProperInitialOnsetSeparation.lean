/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PairSurvivalPropagation
public import Rhone.Statistics.Identifiability.DelayedHistorySeparation
public import Rhone.Statistics.Identifiability.SilentWindowLawSeparation

/-! # Existing continuous time-varying separators need only initial pair properness -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.PairProperness

lemma positive_prefix_of_shifted_exposure (q : ℝ → ℝ) (hq : Continuous q)
    (hqn : ∀ u, 0 ≤ u → 0 ≤ q u) {a : ℝ} (ha : 0 ≤ a)
    (hpost : 0 < ∫ u in (0 : ℝ)..1, q (a + u)) :
    ∃ b : ℝ, 0 ≤ b ∧ 0 < ∫ u in (0 : ℝ)..b, q u := by
  have hs : 0 < ∫ u in a..a + 1, q u := by
    simpa only [intervalIntegral.integral_comp_add_left, add_zero] using hpost
  have hn : 0 ≤ ∫ u in (0 : ℝ)..a, q u :=
    intervalIntegral.integral_nonneg ha (fun u hu => hqn u hu.1)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hq.intervalIntegrable 0 a) (hq.intervalIntegrable a (a + 1))
  exact ⟨a + 1, by linarith, by linarith⟩

theorem jointLaw_probability_initial_proper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a) (hQ : 0 < ∫ u in (0 : ℝ)..a, q u) :
    IsProbabilityMeasure (timeVaryingJointLaw k c q r) :=
  timeVaryingJointLaw_probability_of_pair k c q r hc hq hr hcn hqn hrn
    (fun s _ i => all_pair_tails_of_initial_proper k c q hc hq hqn hproper ha hQ s i)

theorem jointLaw_ne_pan_simultaneous_initial_proper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    (hQ : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, q u)
    (hR : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, r u)
    (hC : ∀ δ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c t)
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw :=
  timeVaryingJointLaw_ne_integrable_pan_of_onset_exposures k c q r hc hq hr hcn hqn hrn
    (fun s _ i => all_pair_tails_of_initial_proper k c q hc hq hqn hproper
      (by norm_num : (0 : ℝ) ≤ 1) (hQ 1 (by norm_num)) s i) hQ hR hC P

theorem jointLaw_ne_pan_delayed_recombination_initial_proper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a) (hbefore : ∀ u ∈ Icc 0 a, r u = 0)
    (hQ : 0 < ∫ u in (0 : ℝ)..a, q u)
    (hR : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, r (a + u))
    (hC : ∀ δ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw :=
  DelayedOnset.jointLaw_ne_pan_of_delayed_recombination k c q r hc hq hr hcn hqn hrn
    (fun s _ i => all_pair_tails_of_initial_proper k c q hc hq hqn hproper ha hQ s i)
    ha hbefore hQ hR hC P

theorem jointLaw_ne_pan_delayed_migration_initial_proper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {a : ℝ} (ha : 0 ≤ a) (hbefore : ∀ u ∈ Icc 0 a, q u = 0)
    (hR : 0 < ∫ u in (0 : ℝ)..a, r u)
    (hQ : ∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, q (a + u))
    (hC : ∀ δ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw := by
  obtain ⟨b, hb, hqb⟩ := positive_prefix_of_shifted_exposure q hq hqn ha (hQ 1 (by norm_num))
  exact DelayedOnset.jointLaw_ne_pan_of_delayed_migration k c q r hc hq hr hcn hqn hrn
    (fun s _ i => all_pair_tails_of_initial_proper k c q hc hq hqn hproper hb hqb s i)
    ha hbefore hR hQ hC P

theorem jointLaw_ne_pan_silent_recombination_initial_proper (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hbefore : ∀ u ∈ Icc 0 a, r u = 0) (hQ : 0 < ∫ u in (0 : ℝ)..a, q u)
    (hsilent : ∀ u ∈ Icc a (a + T), c u = 0 ∧ q u = 0)
    (hR : 0 < ∫ u in (0 : ℝ)..T, r (a + u))
    (hresume : ∀ δ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + T + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw :=
  SilentWindow.jointLaw_ne_pan_of_pure_recombination_silent_window k c q r hc hq hr hcn hqn hrn
    (fun s _ i => all_pair_tails_of_initial_proper k c q hc hq hqn hproper ha hQ s i)
    ha hT hbefore hQ hsilent hR hresume P

end Rhone.Statistics.Identifiability.PairProperness
