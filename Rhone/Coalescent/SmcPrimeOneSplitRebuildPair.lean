/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRebuildOldPair

/-! # Rebuilding supported pair steps preserves the record and the left sample map -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem ARGTransition.coal_successor {pre next : AugmentedState}
    (ht : ARGTransition (pre, next)) (i j : Fin pre.1.2.2.1)
    (hev : next.2.2 = .inr (.inl (i.val, j.val))) :
    next.1 = atTime next.1.1 (coalSuccessor pre.1 i j) := by
  have he : next.2.2 ∈ coalSet := by rw [hev]; exact True.intro
  obtain ⟨a, b, _, hev', hnext, _⟩ := ht.coal_case he
  have hp : (a.val, b.val) = (i.val, j.val) := Sum.inl.inj (Sum.inr.inj (hev'.symm.trans hev))
  have ha : a = i := Fin.ext (congrArg Prod.fst hp)
  have hb : b = j := Fin.ext (congrArg Prod.snd hp)
  subst a
  subst b
  exact hnext

theorem rebuildCoal_supported_pair (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : Fin (N + 1))
    (i j : Fin (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.1)
    (hij : i.val < j.val)
    (hev : (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).2.2 = .inr (.inl (i.val, j.val)))
    (g : Fin N → ℕ) :
    let r : RebuildState N :=
      (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩,
        (extractionRun N h n.val).argLabels, g, (extractionRun N h n.val).detached)
    let r' := rebuildCoal r (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1
      ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 i).1
      ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 j).1
    r'.1 = h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩ ∧
      r'.2.1 = (extractionRun N h (n.val + 1)).argLabels ∧
      r'.2.2.2 = (extractionRun N h n.val).detached := by
  dsimp only
  let r : RebuildState N :=
    (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩,
      (extractionRun N h n.val).argLabels, g, (extractionRun N h n.val).detached)
  have hpre := hs.2.1 ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩
  have hnext := (hs.2.2.1 n).coal_successor i j hev
  have hmark := hs.2.2.2.1 ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩
  constructor
  · rw [rebuildCoal_live r hpre _ i j hij]
    apply Prod.ext
    · exact hnext.symm
    · apply Prod.ext
      · exact hmark.symm
      · exact hev.symm
  · constructor
    · rw [extractionRun_succ N h n.val n.isLt, extractionStep_argLabels, hev]
      simp only [rebuildCoal, rebuildUIDIndex_live _ hpre,
        min_eq_left hij.le, max_eq_right hij.le]
    · rfl

theorem rebuildStep_extracted_old_pair (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : Fin (N + 1))
    (i j : Fin (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.1)
    (hij : i.val < j.val)
    (hev : (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).2.2 = .inr (.inl (i.val, j.val)))
    (hi : (extractionRun N h n.val).detached ≠
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 i).1)
    (hj : (extractionRun N h n.val).detached ≠
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 j).1)
    (g : Fin N → ℕ) :
    let r : RebuildState N :=
      (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩,
        (extractionRun N h n.val).argLabels, g, (extractionRun N h n.val).detached)
    ∃ k : Fin (N - 1), k.val = (extractionRun N h n.val).mergers ∧
      (rebuildStep (extractOneSplitSkeleton N h) r (.inl k)).1 =
        h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩ ∧
      (rebuildStep (extractOneSplitSkeleton N h) r (.inl k)).2.1 =
        (extractionRun N h (n.val + 1)).argLabels ∧
      (rebuildStep (extractOneSplitSkeleton N h) r (.inl k)).2.2.2 =
        (extractionRun N h n.val).detached := by
  dsimp only
  obtain ⟨k, hk, heq⟩ := rebuildStep_extracted_old_pair_eq N h hs n i j hij hev hi hj g
  refine ⟨k, hk, ?_⟩
  rw [heq]
  exact rebuildCoal_supported_pair N h hs n i j hij hev g

theorem extractionRun_old_pair_detached (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n : Fin (N + 1))
    (i j : Fin (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.1)
    (hev : (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).2.2 = .inr (.inl (i.val, j.val)))
    (hi : (extractionRun N h n.val).detached ≠
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 i).1)
    (hj : (extractionRun N h n.val).detached ≠
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 j).1) :
    (extractionRun N h (n.val + 1)).detached = (extractionRun N h n.val).detached := by
  classical
  have hiuid : liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 i.val =
      ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  have hjuid : liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 j.val =
      ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1 := by
    simp only [liveLabelAt, dite_eq_left j.isLt]
  have hhit : ¬ ∃ d, (extractionRun N h n.val).detached = some d ∧
      (d = ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 ∨
        d = ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1) := by
    rintro ⟨d, hd, hdi | hdj⟩
    · exact hi (hd.trans (congrArg some hdi))
    · exact hj (hd.trans (congrArg some hdj))
  rw [extractionRun_succ N h n.val n.isLt]
  simp only [extractionStep, hev, hiuid, hjuid, ite_eq_right hhit]

end Rhone.Coalescent.SmcPrime
