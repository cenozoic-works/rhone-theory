/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableSilentWindow
public import Rhone.Statistics.Identifiability.PairIntegrableMass

/-! # Exhaust all essential support orders for locally L1 symmetric-island histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeIntegrable

lemma positive_exposure_after_divergence (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hdiv : Tendsto (integratedClock f) atTop atTop) (a : ℝ) :
    ∃ b : ℝ, a ≤ b ∧ 0 < ∫ u in a..b, f u := by
  obtain ⟨b, hb, hfb⟩ := exists_lt_of_tendsto_atTop hdiv (a + 1) (integratedClock f a)
  refine ⟨b, by linarith, ?_⟩
  rw [IntegrableExposure.interval_eq_clock_sub f hf]
  linarith

theorem exists_positive_witness_window (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    (hdiv : Tendsto (integratedClock c) atTop atTop)
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ (0 < ∫ u in a..b, c u) ∧
      (∀ t ∈ Ioo a b, 0 < ThreeTimeVarying.witness k c q t) := by
  obtain ⟨a, ha, hqbefore, hqafter⟩ :=
    IntegrableExposure.exists_first_onset_after q hq 0 hqn hA hQ
  obtain ⟨B, hB, hcB⟩ := positive_exposure_after_divergence c hc hdiv a
  have hcn' : ∀ᵐ u, a ≤ u → 0 ≤ c u := by
    filter_upwards [hcn] with u hu hau
    exact hu (ha.trans hau)
  obtain ⟨b, hab, hcbefore, hcafter⟩ :=
    IntegrableExposure.exists_first_onset_after c hc a hcn' hB hcB
  by_cases he : b = a
  · subst b
    obtain ⟨δ, hδ, hW⟩ := witness_positive_after_zero_migration_prefix k c q hc hq hqn ha hqbefore
    refine ⟨a, a + δ, ha, by linarith, hcafter (a + δ) (by linarith), ?_⟩
    intro t ht
    exact hW t ht.1 ht.2 (hqafter t ht.1)
  · have habp : a < b := lt_of_le_of_ne hab (Ne.symm he)
    have hw := witness_positive_after_silent_window k c q hc hq hqn ha hab
      hqbefore hcbefore (hqafter b habp)
    obtain ⟨δ, hδ, hW⟩ := witness_positive_right k c q hc hq hw
    refine ⟨b, b + δ, ha.trans hab, by linarith, hcafter (b + δ) (by linarith), ?_⟩
    intro t ht
    exact hW t ht.1.le ht.2

theorem exists_positive_witness_window_initial_proper (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0))
    {A : ℝ} (hA : 0 ≤ A) (hQ : 0 < integratedClock q A) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ (0 < ∫ u in a..b, c u) ∧
      (∀ t ∈ Ioo a b, 0 < ThreeTimeVarying.witness k c q t) :=
  exists_positive_witness_window k c q hc hq hcn hqn
    (PairIntegrable.coalescence_clock_diverges k c q hc hq hcn hqn hproper) hA hQ

end Rhone.Statistics.Identifiability.ThreeIntegrable
