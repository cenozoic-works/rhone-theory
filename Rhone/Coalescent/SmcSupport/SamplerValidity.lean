/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.SplitSuccessor
public import Rhone.Coalescent.FiniteIntervalMaterialSampler

/-! # The finite-array sampler preserves valid genealogical state data -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem atTime_valid (s : State) (hs : Valid s) (t : ℝ) (ht : 0 ≤ t) :
    Valid (atTime t s) := ⟨ht, hs.2⟩

theorem sampler_clock_nonneg (mode : Mode) (R : ℝ) (s : State)
    (hs : Valid s) (u : Noise) (hu0 : 0 ≤ u 1) (hu1 : u 1 ≤ 1) :
    0 ≤ s.1 - Real.log (u 1) / (totalRate mode R s : ℝ) := by
  have hlog := Real.log_nonpos hu0 hu1
  have hd := div_nonpos_of_nonpos_of_nonneg hlog (totalRate mode R s).property
  exact sub_nonneg.mpr (hd.trans hs.1)

theorem sampleStep_valid (mode : Mode) (R : ℝ) (s : State) (hs : Valid s)
    (u : Noise) (hu0 : 0 ≤ u 1) (hu1 : u 1 ≤ 1)
    (hc0 : 0 < u 2) (hc1 : u 2 < 1) :
    Valid (sampleStep mode R s u).1 := by
  classical
  have ht := sampler_clock_nonneg mode R s hs u hu0 hu1
  unfold sampleStep
  split_ifs
  · exact hs
  · cases ha : selectedAction mode R s u with
    | none => exact hs
    | some a =>
      cases a with
      | inl ij =>
        exact atTime_valid _ (coalSuccessor_valid s hs ij.1 ij.2) _ ht
      | inr i =>
        obtain ⟨hlo, hhi⟩ := affine_cut_interior _ (hs.2.1 i) (u 2) hc0 hc1
        exact atTime_valid _ (splitSuccessor_valid s hs i _ hlo hhi) _ ht

end Rhone.Coalescent.SmcSupport
