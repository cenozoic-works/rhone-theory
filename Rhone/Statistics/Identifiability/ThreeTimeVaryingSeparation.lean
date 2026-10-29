/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingExhaustion
public import Rhone.Statistics.Identifiability.ThreeTimeVaryingPanObstruction

/-! # A time-varying island law with positive migration differs from every pan law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

theorem law_ne_pan_of_positive_migration (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A)
    (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    (htail : Tendsto (integratedClock rate) atTop atTop) :
    law k c q ≠ PanThreeSample.law rate := by
  have hdiv := coalescence_clock_diverges_of_initial_pair k c q hc hq hcn hqn hproper
  obtain ⟨t, ht, hct, hw⟩ := exists_active_positive_witness k c q hc hq hcn hqn hdiv hA hQ
  exact law_ne_pan_of_positive_witness k c q hc hq hcn hqn
    (fun s _ i => PairProperness.all_pair_tails_of_initial_proper k c q hc hq hqn hproper hA hQ s i)
    ht hct hw rate hr hn htail

theorem law_ne_pan_of_positive_migration_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A)
    (rate : ℝ → ℝ) (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    law k c q ≠ PanThreeSample.law rate := by
  intro he
  apply law_ne_pan_of_positive_migration k c q hc hq hcn hqn hproper hA hQ
    (PanThreeSample.nonnegativeRepresentative rate)
    (PanThreeSample.representative_locallyIntegrable hr)
    (PanThreeSample.representative_nonneg rate)
    (PanThreeSample.representative_clock_diverges hn htail)
  exact he.trans (PanThreeSample.law_congr_halfLine_ae (PanThreeSample.representative_eq_ae hn))

lemma positive_exposure_of_positive_rate (q : ℝ → ℝ) (hq : Continuous q)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) (hqt : 0 < q t) :
    0 < integratedClock q (t + 1) :=
  intervalIntegral.integral_pos (by linarith) hq.continuousOn
    (fun u hu => hqn u hu.1.le) ⟨t, ⟨ht, by linarith⟩, hqt⟩

theorem law_ne_pan_of_nonzero_migration (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    (hMigration : ∃ t, 0 ≤ t ∧ 0 < q t)
    (rate : ℝ → ℝ) (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    law k c q ≠ PanThreeSample.law rate := by
  obtain ⟨t, ht, hqt⟩ := hMigration
  exact law_ne_pan_of_positive_migration_ae k c q hc hq hcn hqn hproper (by linarith : 0 ≤ t + 1)
    (positive_exposure_of_positive_rate q hq hqn ht hqt) rate hr hn htail

end Rhone.Statistics.Identifiability.ThreeTimeVarying
