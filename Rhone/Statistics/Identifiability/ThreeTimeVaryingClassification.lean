/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeZeroMigration

/-! # A time-varying island law is pan representable iff migration is zero -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

theorem pan_representable_iff_zero_migration (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧
      Tendsto (integrablePanClock rate) atTop atTop ∧
      law k c q = PanThreeSample.law rate) ↔ (∀ t, 0 ≤ t → q t = 0) := by
  constructor
  · rintro ⟨rate, hr, hn, htail, he⟩ t ht
    by_contra hqzero
    exact law_ne_pan_of_nonzero_migration k c q hc hq hcn hqn hproper
      ⟨t, ht, lt_of_le_of_ne (hqn t ht) (Ne.symm hqzero)⟩ rate hr hn htail he
  · intro hzero
    have hdiv := coalescence_clock_diverges_of_initial_pair k c q hc hq hcn hqn hproper
    have he : integratedClock c =ᶠ[atTop] integrablePanClock c := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact PanThreeSample.clock_eq_halfLine c ht
    exact ⟨c, hc.locallyIntegrable.locallyIntegrableOn (Ici 0), Filter.Eventually.of_forall hcn,
      hdiv.congr' he, law_zero_migration_halfLine k c q hc hq hzero⟩

end Rhone.Statistics.Identifiability.ThreeTimeVarying
