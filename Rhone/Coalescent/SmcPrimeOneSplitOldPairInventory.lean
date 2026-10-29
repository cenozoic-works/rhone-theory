/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitOldLookups
public import Rhone.Coalescent.SmcPrimeOneSplitExtractionRun

/-! # Old pair successors preserve the extracted lineage inventory -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionStep_old_pair_inventory {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (h : ExtractionInventory z pre.1) (hs : Valid pre.1)
    (ht : 0 ≤ next.1.1) (i j : Fin pre.1.2.2.1) (hij : i.val < j.val)
    (hev : next.2.2 = .inr (.inl (i.val, j.val)))
    (hnext : next.1 = atTime next.1.1 (coalSuccessor pre.1 i j))
    (hi : z.detached ≠ some (pre.1.2.2.2 i).1)
    (hj : z.detached ≠ some (pre.1.2.2.2 j).1) :
    ExtractionInventory (extractionStep z pre next) next.1 := by
  classical
  obtain ⟨a, u, haf, hag, hlu⟩ := h.parent_lookup i hi
  obtain ⟨b, v, hbf, hbg, hlv⟩ := h.parent_lookup j hj
  have hne : u ≠ v := by
    intro he
    have hge : z.oldLabels a = z.oldLabels b := by rw [hag, hbg, he]
    have hfe := (h.2.2.2.2 a b).mpr hge
    have heij := hs.2.2.2 (haf.symm.trans (hfe.trans hbf))
    exact (ne_of_lt hij) (congrArg Fin.val heij)
  have hiuid : liveLabelAt pre.1 i.val = (pre.1.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  have hjuid : liveLabelAt pre.1 j.val = (pre.1.2.2.2 j).1 := by
    simp only [liveLabelAt, dite_eq_left j.isLt]
  have hnattach : ¬ ∃ d, z.detached = some d ∧
      (d = (pre.1.2.2.2 i).1 ∨ d = (pre.1.2.2.2 j).1) := by
    rintro ⟨d, hd, hdi | hdj⟩
    · exact hi (hd.trans (congrArg some hdi))
    · exact hj (hd.trans (congrArg some hdj))
  have hdet : (extractionStep z pre next).detached = z.detached := by
    simp only [extractionStep, hev, hiuid, hjuid, ite_eq_right hnattach]
  have hlabels : (extractionStep z pre next).oldLabels =
      fun k => if z.oldLabels k = z.oldLabels a ∨ z.oldLabels k = z.oldLabels b
        then z.old.1.2.1 else z.oldLabels k := by
    simp only [extractionStep, hev, hiuid, hjuid, ite_eq_right hnattach, hlu, hlv]
    rw [rebuildCoal_sample_labels (z.old, z.oldLabels, z.oldLabels, none)
      h.1 next.1.1 u v hne]
    rw [hag, hbg]
  have hphyslabels : (extractionStep z pre next).argLabels =
      fun k => if z.argLabels k = (pre.1.2.2.2 i).1 ∨
          z.argLabels k = (pre.1.2.2.2 j).1 then pre.1.2.1 else z.argLabels k := by
    rw [extractionStep_argLabels, hev]
    funext k
    exact ancestorStep_pair_labels pre.1 i j hij _ _
  obtain ⟨p, q, hpq, hold, hgold⟩ :=
    extractionStep_old_pair z pre next h hs i j hij hev hi hj
  have holdvalid : Valid (extractionStep z pre next).old.1 := by
    rw [hold]
    exact SmcSupport.atTime_valid _ (SmcSupport.coalSuccessor_valid _ h.1 p q) _ ht
  have hphysical : ARGLeftInventory next.1
      (extractionStep z pre next).argLabels (extractionStep z pre next).detached := by
    rw [hnext, hphyslabels, hdet]
    simpa only [atTime, ARGLeftInventory,
      ite_eq_right (not_or_intro hi hj)] using h.2.1.coal hs i j hij
  have hgoldInv : ARGLeftInventory z.old.1 z.oldLabels none := by
    exact ⟨h.2.2.1, fun k => Or.inl (h.2.2.2.1 k), fun _ hh => by cases hh⟩
  have hgnew : ARGLeftInventory (extractionStep z pre next).old.1
      (extractionStep z pre next).oldLabels none := by
    rw [hold, hgold]
    simpa only [atTime, ARGLeftInventory, ancestorStep_pair_labels _ p q hpq,
      reduceCtorEq, or_self, ite_false] using hgoldInv.coal h.1 p q hpq
  refine ⟨holdvalid, hphysical, hgnew.1, ?_, ?_⟩
  · intro k
    rcases hgnew.2.1 k with hh | hh
    · exact hh
    · cases hh
  · rw [hphyslabels, hlabels, ← haf, ← hbf]
    exact sameLeftPartition_merge z.argLabels z.oldLabels h.2.2.2.2 a b _ _
      (fun k => ne_of_lt (h.2.1.sample_lt_fresh hs k))
      (fun k => ne_of_lt (hgoldInv.sample_lt_fresh h.1 k))

end Rhone.Coalescent.SmcPrime
