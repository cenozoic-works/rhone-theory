/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegratedClock
public import Mathlib.Topology.Order.Monotone

/-! # Essential exposure onsets for locally L1 rates, independent of null-set representatives -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.IntegrableExposure

lemma interval_nonnegative (f : ℝ → ℝ) {a s t : ℝ} (has : a ≤ s) (hst : s ≤ t)
    (hn : ∀ᵐ u, a ≤ u → 0 ≤ f u) : 0 ≤ ∫ u in s..t, f u := by
  apply intervalIntegral.integral_nonneg_of_ae_restrict hst
  filter_upwards [hn.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Icc] with u hu hmem
  exact hu (has.trans hmem.1)

lemma interval_eq_clock_sub (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (a t : ℝ) :
    (∫ u in a..t, f u) = integratedClock f t - integratedClock f a := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (locallyIntegrable_interval f hf 0 a) (locallyIntegrable_interval f hf a t)
  unfold integratedClock
  linarith

lemma interval_clock_continuous (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (a : ℝ) :
    Continuous (fun t => ∫ u in a..t, f u) := by
  simp_rw [interval_eq_clock_sub f hf]
  exact (integratedClock_continuous f hf).sub continuous_const

lemma interval_clock_monotone (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    {a s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (hn : ∀ᵐ u, a ≤ u → 0 ≤ f u) :
    (∫ u in a..s, f u) ≤ ∫ u in a..t, f u := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (locallyIntegrable_interval f hf a s) (locallyIntegrable_interval f hf s t)
  have hp := interval_nonnegative f has hst hn
  linarith

lemma ae_zero_of_exposure_zero (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    {a t : ℝ} (hat : a ≤ t) (hn : ∀ᵐ u, a ≤ u → 0 ≤ f u)
    (hz : (∫ u in a..t, f u) = 0) : ∀ᵐ u, u ∈ Icc a t → f u = 0 := by
  have hnr : 0 ≤ᵐ[volume.restrict (Ioc a t)] f := by
    filter_upwards [hn.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioc] with u hu hmem
    exact hu hmem.1.le
  rw [intervalIntegral.integral_of_le hat] at hz
  have hzr := (integral_eq_zero_iff_of_nonneg_ae hnr
    (locallyIntegrable_interval f hf a t).1).mp hz
  have hglob := (ae_restrict_iff' measurableSet_Ioc).mp hzr
  filter_upwards [hglob, volume.ae_ne a] with u hu hne hmem
  exact hu ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩

theorem exists_first_onset_after (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (a : ℝ) (hn : ∀ᵐ u, a ≤ u → 0 ≤ f u)
    {b : ℝ} (hab : a ≤ b) (hpositive : 0 < ∫ u in a..b, f u) :
    ∃ s : ℝ, a ≤ s ∧ (∀ᵐ u, u ∈ Icc a s → f u = 0) ∧
      (∀ t, s < t → 0 < ∫ u in s..t, f u) := by
  let H := fun t => ∫ u in a..t, f u
  let Z : Set ℝ := {t | a ≤ t ∧ H t = 0}
  have hZ : Z.Nonempty := ⟨a, le_rfl, by simp [H]⟩
  have hclosed : IsClosed Z := isClosed_Ici.inter
    (isClosed_eq (interval_clock_continuous f hf a) continuous_const)
  have hbounded : BddAbove Z := by
    refine ⟨b, fun u hu => ?_⟩
    by_contra h
    have hp := hpositive.trans_le
      (interval_clock_monotone f hf hab (lt_of_not_ge h).le hn)
    exact hp.ne' hu.2
  let s := sSup Z
  have hmem : s ∈ Z := hclosed.csSup_mem hZ hbounded
  have has : a ≤ s := hmem.1
  have hzero : H s = 0 := hmem.2
  refine ⟨s, has, ae_zero_of_exposure_zero f hf has hn hzero, ?_⟩
  intro t hst
  have hnn : 0 ≤ H t := interval_nonnegative f le_rfl (has.trans hst.le) hn
  have hnz : H t ≠ 0 := by
    intro hz
    have ht : t ≤ s := le_csSup hbounded ⟨has.trans hst.le, hz⟩
    exact hst.not_ge ht
  have hp : 0 < H t := lt_of_le_of_ne hnn (Ne.symm hnz)
  have he := intervalIntegral.integral_add_adjacent_intervals
    (locallyIntegrable_interval f hf a s) (locallyIntegrable_interval f hf s t)
  change (∫ u in a..s, f u) = 0 at hzero
  change 0 < ∫ u in a..t, f u at hp
  linarith

end Rhone.Statistics.Identifiability.IntegrableExposure
