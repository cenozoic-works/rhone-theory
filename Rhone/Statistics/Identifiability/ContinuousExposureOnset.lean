/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegratedClock
public import Mathlib.Topology.Order.Monotone

/-! # First essential onsets for continuous nonnegative histories, including flat supports -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ExposureOnset

lemma clock_nonnegative (f : ℝ → ℝ) (hn : ∀ u, 0 ≤ u → 0 ≤ f u)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ integratedClock f t :=
  intervalIntegral.integral_nonneg ht (fun u hu => hn u hu.1)

lemma clock_monotone (f : ℝ → ℝ) (hf : Continuous f) (hn : ∀ u, 0 ≤ u → 0 ≤ f u)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : integratedClock f s ≤ integratedClock f t := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 s) (hf.intervalIntegrable s t)
  have hp : 0 ≤ ∫ u in s..t, f u :=
    intervalIntegral.integral_nonneg hst (fun u hu => hn u (hs.trans hu.1))
  unfold integratedClock
  linarith

theorem exists_first_onset (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ u, 0 ≤ u → 0 ≤ f u) {b : ℝ} (hb : 0 ≤ b)
    (hpositive : 0 < integratedClock f b) :
    ∃ a : ℝ, 0 ≤ a ∧ (∀ u ∈ Ioo 0 a, f u = 0) ∧
      (∀ t, 0 < t → 0 < ∫ u in (0 : ℝ)..t, f (a + u)) := by
  let Z : Set ℝ := {t | 0 ≤ t ∧ integratedClock f t = 0}
  have hZ : Z.Nonempty := ⟨0, le_rfl, by simp [integratedClock]⟩
  have hclosed : IsClosed Z :=
    isClosed_Ici.inter
      (isClosed_eq (integratedClock_continuous f hf.locallyIntegrable) continuous_const)
  have hbounded : BddAbove Z := by
    refine ⟨b, fun u hu => ?_⟩
    by_contra h
    have hbu : b ≤ u := (lt_of_not_ge h).le
    have hp := hpositive.trans_le (clock_monotone f hf hn hb hbu)
    exact hp.ne' hu.2
  let a := sSup Z
  have hamem : a ∈ Z := hclosed.csSup_mem hZ hbounded
  have ha : 0 ≤ a := hamem.1
  have hFa : integratedClock f a = 0 := hamem.2
  have hafter (u : ℝ) (hu : a < u) : 0 < integratedClock f u := by
    have hnn := clock_nonnegative f hn (ha.trans hu.le)
    have hnz : integratedClock f u ≠ 0 := by
      intro hz
      have hle : u ≤ a := le_csSup hbounded ⟨ha.trans hu.le, hz⟩
      exact hu.not_ge hle
    exact lt_of_le_of_ne hnn (Ne.symm hnz)
  refine ⟨a, ha, ?_, ?_⟩
  · intro u hu
    by_contra hne
    have hp : 0 < f u := lt_of_le_of_ne (hn u hu.1.le) (Ne.symm hne)
    have hi := intervalIntegral.integral_pos (hu.1.trans hu.2) hf.continuousOn
      (fun v hv => hn v hv.1.le) ⟨u, ⟨hu.1.le, hu.2.le⟩, hp⟩
    exact hi.ne' hFa
  · intro t ht
    rw [intervalIntegral.integral_comp_add_left, add_zero]
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a (a + t))
    have hp := hafter (a + t) (by linarith)
    unfold integratedClock at hFa hp
    linarith

theorem exists_positive_interior (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ u, 0 ≤ u → 0 ≤ f u) {T : ℝ} (hT : 0 < T)
    (hpositive : 0 < ∫ u in (0 : ℝ)..T, f u) :
    ∃ u, 0 < u ∧ u < T ∧ 0 < f u := by
  by_contra! h
  have he : EqOn f (fun _ => 0) (Ioo 0 T) := by
    intro u hu
    exact le_antisymm (h u hu.1 hu.2) (hn u hu.1.le)
  have hcl := he.closure hf continuous_const
  rw [closure_Ioo (ne_of_lt hT)] at hcl
  have hz : (∫ u in (0 : ℝ)..T, f u) = 0 := by
    calc
      _ = ∫ _u in (0 : ℝ)..T, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hT.le] at hu
        exact hcl hu
      _ = 0 := by simp
  exact hpositive.ne' hz

theorem shifted_exposure_of_divergence (f : ℝ → ℝ) (hf : Continuous f)
    (hdiv : Tendsto (integratedClock f) atTop atTop) (a : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ 0 < ∫ u in (0 : ℝ)..T, f (a + u) := by
  obtain ⟨b, hb, hfb⟩ := exists_lt_of_tendsto_atTop hdiv (a + 1) (integratedClock f a)
  refine ⟨b - a, by linarith, ?_⟩
  rw [intervalIntegral.integral_comp_add_left, add_zero, add_sub_cancel]
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
  unfold integratedClock at hfb
  linarith

end Rhone.Statistics.Identifiability.ExposureOnset
