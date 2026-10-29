/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableClassification

/-! # Local integrability is needed only on the nonnegative half-line -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma extension_nonnegative_ae (f : ℝ → ℝ) (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ f t) :
    ∀ᵐ t, 0 ≤ t → 0 ≤ panZeroExtension f t := by
  filter_upwards [hn] with t ht ht0
  rw [panZeroExtension_of_nonneg f ht0]
  exact ht ht0

lemma extension_ae_zero_iff (f : ℝ → ℝ) :
    (∀ᵐ t, 0 ≤ t → panZeroExtension f t = 0) ↔ (∀ᵐ t, 0 ≤ t → f t = 0) := by
  constructor
  · intro he
    filter_upwards [he] with t ht ht0
    simpa only [panZeroExtension_of_nonneg f ht0] using ht ht0
  · intro he
    filter_upwards [he] with t ht ht0
    simpa only [panZeroExtension_of_nonneg f ht0] using ht ht0

theorem halfLine_pan_representable_iff_zero_migration_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrableOn c (Ici 0) volume) (hq : LocallyIntegrableOn q (Ici 0) volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k (panZeroExtension c) (panZeroExtension q) 0 0)
      atTop (𝓝 0)) :
    (∃ rate : ℝ → ℝ, LocallyIntegrableOn rate (Ici 0) volume ∧
      (∀ᵐ t, 0 ≤ t → 0 ≤ rate t) ∧
      Tendsto (integrablePanClock rate) atTop atTop ∧
      law k (panZeroExtension c) (panZeroExtension q) = PanThreeSample.law rate) ↔
        (∀ᵐ t, 0 ≤ t → q t = 0) :=
  (pan_representable_iff_zero_migration_ae k (panZeroExtension c) (panZeroExtension q)
    (panZeroExtension_locallyIntegrable hc) (panZeroExtension_locallyIntegrable hq)
    (extension_nonnegative_ae c hcn) (extension_nonnegative_ae q hqn) hproper).trans
      (extension_ae_zero_iff q)

end Rhone.Statistics.Identifiability.ThreeIntegrable
