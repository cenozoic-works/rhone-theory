/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitLeftInventorySuccessors
public import Rhone.Coalescent.SmcPrimeOneSplitExtractionRun

/-! # Cut and attachment steps preserve the old left-history inventory -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionStep_split_inventory {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (h : ExtractionInventory z pre.1) (hs : Valid pre.1)
    (hd : z.detached = none) (i : Fin pre.1.2.2.1) (x : ℝ) (hx : 0 < x)
    (hev : next.2.2 = .inr (.inr (i.val, x)))
    (hnext : next.1 = atTime next.1.1 (splitSuccessor pre.1 i x)) :
    ExtractionInventory (extractionStep z pre next) next.1 := by
  have hfields : (extractionStep z pre next).old = z.old ∧
      (extractionStep z pre next).oldLabels = z.oldLabels ∧
      (extractionStep z pre next).detached = some (pre.1.2.1 + 1) := by
    simp only [extractionStep, hev]
    exact ⟨True.intro, True.intro, True.intro⟩
  have hlabels : (extractionStep z pre next).argLabels =
      fun a => if z.argLabels a = (pre.1.2.2.2 i).1
        then pre.1.2.1 else z.argLabels a := by
    rw [extractionStep_argLabels, hev]
    funext a
    exact ancestorStep_split_left _ i x hx _
  have hp : ARGLeftInventory pre.1 z.argLabels none := by
    simpa only [hd] using h.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfields.1]
    exact h.1
  · rw [hnext, hlabels, hfields.2.2]
    exact hp.split hs i x
  · rw [hfields.1, hfields.2.1]
    exact h.2.2.1
  · rw [hfields.1, hfields.2.1]
    exact h.2.2.2.1
  · rw [hlabels, hfields.2.1]
    exact h.2.2.2.2.replace_fresh _ _
      (fun a => ne_of_lt (hp.sample_lt_fresh hs a))

theorem extractionStep_attachment_inventory {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (h : ExtractionInventory z pre.1) (hs : Valid pre.1)
    (i j : Fin pre.1.2.2.1) (hij : i.val < j.val)
    (hev : next.2.2 = .inr (.inl (i.val, j.val)))
    (hnext : next.1 = atTime next.1.1 (coalSuccessor pre.1 i j))
    (hd : z.detached = some (pre.1.2.2.2 i).1 ∨
      z.detached = some (pre.1.2.2.2 j).1) :
    ExtractionInventory (extractionStep z pre next) next.1 := by
  classical
  have hiuid : liveLabelAt pre.1 i.val = (pre.1.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  have hjuid : liveLabelAt pre.1 j.val = (pre.1.2.2.2 j).1 := by
    simp only [liveLabelAt, dite_eq_left j.isLt]
  have hattach : ∃ d, z.detached = some d ∧
      (d = (pre.1.2.2.2 i).1 ∨ d = (pre.1.2.2.2 j).1) := by
    rcases hd with hi | hj
    · exact ⟨_, hi, Or.inl rfl⟩
    · exact ⟨_, hj, Or.inr rfl⟩
  have hfields : (extractionStep z pre next).old = z.old ∧
      (extractionStep z pre next).oldLabels = z.oldLabels ∧
      (extractionStep z pre next).detached = none := by
    simp only [extractionStep, hev, hiuid, hjuid, ite_eq_left hattach]
    exact ⟨True.intro, True.intro, True.intro⟩
  have hlabels : (extractionStep z pre next).argLabels =
      fun a => if z.argLabels a = (pre.1.2.2.2 i).1 ∨
        z.argLabels a = (pre.1.2.2.2 j).1 then pre.1.2.1 else z.argLabels a := by
    rw [extractionStep_argLabels, hev]
    funext a
    exact ancestorStep_pair_labels _ i j hij _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfields.1]
    exact h.1
  · rw [hnext, hlabels, hfields.2.2]
    simpa only [ite_eq_left hd, atTime, ARGLeftInventory] using h.2.1.coal hs i j hij
  · rw [hfields.1, hfields.2.1]
    exact h.2.2.1
  · rw [hfields.1, hfields.2.1]
    exact h.2.2.2.1
  · rw [hlabels, hfields.2.1]
    rcases hd with hi | hj
    · have hnot := (h.2.1.2.2 _ hi).2
      simpa only [hnot, false_or] using h.2.2.2.2.replace_fresh
        (pre.1.2.2.2 j).1 pre.1.2.1
        (fun a => ne_of_lt (h.2.1.sample_lt_fresh hs a))
    · have hnot := (h.2.1.2.2 _ hj).2
      simpa only [hnot, or_false] using h.2.2.2.2.replace_fresh
        (pre.1.2.2.2 i).1 pre.1.2.1
        (fun a => ne_of_lt (h.2.1.sample_lt_fresh hs a))

end Rhone.Coalescent.SmcPrime
