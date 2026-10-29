/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.StateSupport
public import Rhone.Coalescent.FiniteIntervalMaterialSampler

/-! # Restricted and unrestricted sampler modes agree when all lineages touch -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem zeroSplit_contacts {s : State} (hs : ZeroSplitReachable s)
    (i j : Fin s.2.2.1) : touches (s.2.2.2 i).2 (s.2.2.2 j).2 := by
  have hf := zeroSplit_full hs
  have h := fun k => full_anchored 0 (by norm_num) (by norm_num) _ (hf k)
  exact ⟨(h i).1.trans (h j).2, (h j).1.trans (h i).2⟩

theorem candidateRate_agreement (R : ℝ) (s : State)
    (hs : ∀ i j, touches (s.2.2.2 i).2 (s.2.2.2 j).2) :
    candidateRate false R s = candidateRate true R s := by
  classical
  funext a
  cases a with
  | inl ij => simp [candidateRate, hs ij.1 ij.2]
  | inr i => rfl

theorem markedLaw_agreement (R : ℝ) (s : State)
    (hs : ∀ i j, touches (s.2.2.2 i).2 (s.2.2.2 j).2) :
    markedLaw false R s = markedLaw true R s := by
  have hr := candidateRate_agreement R s hs
  simp only [markedLaw, rawMarkedLaw, totalRate, hr]
  rfl

theorem sampleStep_agreement (R : ℝ) (s : State) (u : Noise)
    (hs : ∀ i j, touches (s.2.2.2 i).2 (s.2.2.2 j).2) :
    sampleStep false R s u = sampleStep true R s u := by
  have hr := candidateRate_agreement R s hs
  simp only [sampleStep, selectedAction, totalRate, hr]
  rfl

theorem sampleStep_zeroSplit (R : ℝ) {s : State}
    (hs : ZeroSplitReachable s) (u : Noise) :
    sampleStep false R s u = sampleStep true R s u :=
  sampleStep_agreement R s u (zeroSplit_contacts hs)

theorem sampleStep_oneSplit (R x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : State} (hs : OneSplitReachable x s) (u : Noise) :
    sampleStep false R s u = sampleStep true R s u :=
  sampleStep_agreement R s u (oneSplit_contacts x hx0 hx1 hs)

end Rhone.Coalescent.SmcSupport
