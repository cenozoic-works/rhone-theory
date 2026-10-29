/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRebuildPair
public import Rhone.Coalescent.SmcPrimeOneSplitAttachmentFields

/-! # Rebuilding the detached-parent pair from the extracted attachment -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem OneSplitPrefixSupported.after_detached_no_split {N : ℕ}
    {h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)} (hs : OneSplitPrefixSupported N h)
    (n : ℕ) (_hn : n ≤ N + 1) (d : ℕ)
    (hd : (extractionRun N h n).detached = some d) :
    ∀ m, n ≤ m → CoalOrStop (extractionPrefixExtension N h (m + 1)).2.2 := by
  obtain ⟨c, _, hcoal⟩ := hs.2.2.2.2.1
  have hcn : c.val < n := by
    by_contra hh
    have hnone := extractionRun_detached_before_split N h c hcoal n (by omega)
    rw [hd] at hnone
    cases hnone
  intro m hm
  exact extractionPrefixExtension_no_other_split N h c hcoal m (by omega)

theorem rebuildStep_extracted_attachment_eq (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : Fin (N + 1))
    (i j : Fin (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.1)
    (hij : i.val < j.val)
    (hev : (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).2.2 = .inr (.inl (i.val, j.val)))
    (hd : (extractionRun N h n.val).detached =
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 i).1 ∨
      (extractionRun N h n.val).detached =
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 j).1)
    (g : Fin N → ℕ) :
    let r : RebuildState N :=
      (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩,
        (extractionRun N h n.val).argLabels, g, (extractionRun N h n.val).detached)
    let r' := rebuildCoal r (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1
      ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 i).1
      ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 j).1
    rebuildStep (extractOneSplitSkeleton N h) r (.inr true) =
      (r'.1, r'.2.1, r'.2.2.1, none) := by
  classical
  dsimp only
  have hpre := hs.2.1 ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩
  have hinv := extractionRun_inventory N h hs n.val n.isLt.le
  have hiuid : liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 i.val =
      ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  have hjuid : liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 j.val =
      ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1 := by
    simp only [liveLabelAt, dite_eq_left j.isLt]
  have hevω : (extractionPrefixExtension N h (n.val + 1)).2.2 =
      .inr (.inl (i.val, j.val)) := by
    rw [extractionPrefixExtension_prefix N h (n.val + 1) n.isLt]
    exact hev
  have hhit : ∃ d, (extractionRun N h n.val).detached = some d ∧
      (d = liveLabelAt (extractionPrefixExtension N h n.val).1 i.val ∨
        d = liveLabelAt (extractionPrefixExtension N h n.val).1 j.val) := by
    rw [extractionPrefixExtension_prefix N h n.val n.isLt.le, hiuid, hjuid]
    rcases hd with hi | hj
    · exact ⟨_, hi, Or.inl rfl⟩
    · exact ⟨_, hj, Or.inr rfl⟩
  have hother : ∀ m, n.val < m →
      CoalOrStop (extractionPrefixExtension N h (m + 1)).2.2 := by
    obtain ⟨d, hdd, _⟩ := hhit
    intro m hm
    exact hs.after_detached_no_split n.val n.isLt.le d hdd m hm.le
  have hfields := extractOneSplitSkeleton_attachment_fields N h n.val n.isLt
    (i.val, j.val) hevω hhit hother
  have hf : (fun a => ancestorLabel N (extractionPrefixExtension N h)
      leftBoundaryProbe a n.val) = (extractionRun N h n.val).argLabels := by
    funext a
    exact (extractionRun_argLabels N h n.val n.isLt.le a).symm
  rw [hf, extractionPrefixExtension_prefix N h n.val n.isLt.le,
    extractionPrefixExtension_prefix N h (n.val + 1) n.isLt, hiuid, hjuid] at hfields
  have hne : ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 ≠
      ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1 := by
    intro he
    exact (ne_of_lt hij) (congrArg Fin.val (hpre.2.2.2 he))
  rcases hd with hi | hj
  · have hnj : (extractionRun N h n.val).detached ≠
        some ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1 := by
      intro hh
      exact hne (Option.some.inj (hi.symm.trans hh))
    have hlu := hinv.2.1.rebuild_clade j hnj
    simp only [rebuildStep, hfields, hi, ite_true, hlu]
  · have hni : (extractionRun N h n.val).detached ≠
        some ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 := by
      intro hh
      exact hne (Option.some.inj (hh.symm.trans hj))
    have hlu := hinv.2.1.rebuild_clade i hni
    have hsome : some ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1 ≠
        some ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 := by
      intro hh
      exact hne (Option.some.inj hh).symm
    simp only [rebuildStep, hfields, hj, ite_eq_right hsome, hlu]
    rw [rebuildCoal_swap]

theorem extractionRun_attachment_detached_none (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n : Fin (N + 1))
    (i j : Fin (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.1)
    (hev : (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).2.2 = .inr (.inl (i.val, j.val)))
    (hd : (extractionRun N h n.val).detached =
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 i).1 ∨
      (extractionRun N h n.val).detached =
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 j).1) :
    (extractionRun N h (n.val + 1)).detached = none := by
  have hiuid : liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 i.val =
      ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  have hjuid : liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 j.val =
      ((h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1.2.2.2 j).1 := by
    simp only [liveLabelAt, dite_eq_left j.isLt]
  have hhit : ∃ d, (extractionRun N h n.val).detached = some d ∧
      (d = liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 i.val ∨
        d = liveLabelAt (h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩).1 j.val) := by
    rw [hiuid, hjuid]
    rcases hd with hi | hj
    · exact ⟨_, hi, Or.inl rfl⟩
    · exact ⟨_, hj, Or.inr rfl⟩
  rw [extractionRun_succ N h n.val n.isLt]
  exact (extractionStep_attachment_field _ _ _ (i.val, j.val) hev hhit).1

theorem rebuildStep_extracted_attachment (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (n : Fin (N + 1))
    (i j : Fin (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.1)
    (hij : i.val < j.val)
    (hev : (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).2.2 = .inr (.inl (i.val, j.val)))
    (hd : (extractionRun N h n.val).detached =
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 i).1 ∨
      (extractionRun N h n.val).detached =
      some ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 j).1)
    (g : Fin N → ℕ) :
    let r : RebuildState N :=
      (h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩,
        (extractionRun N h n.val).argLabels, g, (extractionRun N h n.val).detached)
    let r' := rebuildStep (extractOneSplitSkeleton N h) r (.inr true)
    r'.1 = h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩ ∧
      r'.2.1 = (extractionRun N h (n.val + 1)).argLabels ∧
      r'.2.2.2 = (extractionRun N h (n.val + 1)).detached := by
  dsimp only
  rw [rebuildStep_extracted_attachment_eq N h hs n i j hij hev hd g]
  have hpair := rebuildCoal_supported_pair N h hs n i j hij hev g
  refine ⟨hpair.1, hpair.2.1, ?_⟩
  exact (extractionRun_attachment_detached_none N h n i j hev hd).symm

end Rhone.Coalescent.SmcPrime
