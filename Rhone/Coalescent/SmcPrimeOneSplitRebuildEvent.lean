/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRebuildCut
public import Rhone.Coalescent.SmcPrimeOneSplitRebuildAttachment
public import Rhone.Coalescent.SmcPrimeOneSplitEventTrace

/-! # Each classified event rebuilds the next ARG record -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem rebuildStep_extractionRebuildEvent (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : Fin (N + 1)) (g : Fin N → ℕ) :
    let pre := h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩
    let next := h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩
    let r : RebuildState N :=
      (pre, (extractionRun N h n.val).argLabels, g,
        (extractionRun N h n.val).detached)
    let r' := rebuildStep (extractOneSplitSkeleton N h) r
      (extractionRebuildEvent N (extractionRun N h n.val) pre next)
    r'.1 = next ∧ r'.2.1 = (extractionRun N h (n.val + 1)).argLabels ∧
      r'.2.2.2 = (extractionRun N h (n.val + 1)).detached := by
  classical
  dsimp only
  obtain ⟨s, hsplit, hcoal⟩ := hs.2.2.2.2.1
  by_cases hn : n = s
  · have hspl : (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).2.2 ∈ splitSet := by
      simpa only [← hn] using hsplit
    obtain ⟨i, x, _, _, hev, _, _⟩ := (hs.2.2.1 n).split_case (hs.2.1 _) hspl
    simp only [extractionRebuildEvent, hev]
    exact rebuildStep_extracted_cut N h hs n i x hev g
  · obtain ⟨i, j, hij, hev, _, _⟩ := (hs.2.2.1 n).coal_case (hcoal n hn)
    have hiuid : liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 i.val =
        ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 := by
      simp only [liveLabelAt, dite_eq_left i.isLt]
    have hjuid : liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 j.val =
        ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1 := by
      simp only [liveLabelAt, dite_eq_left j.isLt]
    by_cases hd : (extractionRun N h n.val).detached =
        some ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 ∨
        (extractionRun N h n.val).detached =
        some ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1
    · have hhit : ∃ d, (extractionRun N h n.val).detached = some d ∧
          (d = ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 ∨
            d = ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1) := by
        rcases hd with hi | hj
        · exact ⟨_, hi, Or.inl rfl⟩
        · exact ⟨_, hj, Or.inr rfl⟩
      simp only [extractionRebuildEvent, hev, hiuid, hjuid, ite_eq_left hhit]
      exact rebuildStep_extracted_attachment N h hs n i j hij hev hd g
    · have hi := fun hh => hd (Or.inl hh)
      have hj := fun hh => hd (Or.inr hh)
      have hhit : ¬ ∃ d, (extractionRun N h n.val).detached = some d ∧
          (d = ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 ∨
            d = ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1) := by
        rintro ⟨d, hdd, hdi | hdj⟩
        · exact hi (hdd.trans (congrArg some hdi))
        · exact hj (hdd.trans (congrArg some hdj))
      obtain ⟨k, hk, hrecord, hleft, hdet⟩ :=
        rebuildStep_extracted_old_pair N h hs n i j hij hev hi hj g
      have hb : (extractionRun N h n.val).mergers < N - 1 := by rw [← hk]; exact k.isLt
      simp only [extractionRebuildEvent, hev, hiuid, hjuid, ite_eq_right hhit, dite_eq_left hb]
      have hik : (⟨(extractionRun N h n.val).mergers, hb⟩ : Fin (N - 1)) = k :=
        Fin.ext hk.symm
      rw [hik]
      exact ⟨hrecord, hleft, hdet.trans (extractionRun_old_pair_detached N h n i j hev hi hj).symm⟩

end Rhone.Coalescent.SmcPrime
