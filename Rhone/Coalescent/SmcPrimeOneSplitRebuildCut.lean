/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitCutBranch

/-! # Rebuilding the cut step from the extracted cut -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem rebuildStep_extracted_cut (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (c : Fin (N + 1))
    (i : Fin (h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1.2.2.1)
    (x : ℝ)
    (hev : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 = .inr (.inr (i.val, x)))
    (g : Fin N → ℕ) :
    let r : RebuildState N :=
      (h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩,
        (extractionRun N h c.val).argLabels, g, (extractionRun N h c.val).detached)
    let r' := rebuildStep (extractOneSplitSkeleton N h) r (.inr false)
    r'.1 = h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩ ∧
      r'.2.1 = (extractionRun N h (c.val + 1)).argLabels ∧
      r'.2.2.2 = (extractionRun N h (c.val + 1)).detached := by
  classical
  dsimp only
  let r : RebuildState N :=
    (h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩,
      (extractionRun N h c.val).argLabels, g, (extractionRun N h c.val).detached)
  have he : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 ∈ splitSet := by
    rw [hev]
    exact True.intro
  have hd := hs.detached_before_cut c he
  have hother := extractionPrefixExtension_no_other_split N h c (hs.cut_other_coal c he)
  have hevω : (extractionPrefixExtension N h (c.val + 1)).2.2 =
      .inr (.inr (i.val, x)) := by
    rw [extractionPrefixExtension_prefix N h (c.val + 1) c.isLt]
    exact hev
  have hcoords := extractOneSplitSkeleton_cut_coordinates N h c i.val x hevω hother
  rw [extractionPrefixExtension_prefix N h (c.val + 1) c.isLt] at hcoords
  obtain ⟨_, _, _, hclade⟩ := extractOneSplitSkeleton_cut_branch N h hs c i x hev
  have hlookup := (extractionRun_inventory N h hs c.val c.isLt.le).2.1.rebuild_clade i
    (by rw [hd]; exact nofun)
  have hstep : rebuildStep (extractOneSplitSkeleton N h) r (.inr false) =
      rebuildSplit r (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 x
        ((h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1.2.2.2 i).1 := by
    simp only [rebuildStep, hcoords.1, hcoords.2, hclade, r, hlookup]
  have hpre := hs.2.1 ⟨c.val, Finset.mem_Iic.mpr c.isLt.le⟩
  have hsplit := hs.cut_successor c i x hev
  have htmark := hs.2.2.2.1 ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩
  change (rebuildStep (extractOneSplitSkeleton N h) r (.inr false)).1 = _ ∧ _ ∧ _
  rw [hstep]
  constructor
  · rw [rebuildSplit_live r hpre _ x i]
    apply Prod.ext
    · exact hsplit.2.2.2.symm
    · apply Prod.ext
      · exact htmark.symm
      · exact hev.symm
  · rw [extractionRun_succ N h c.val c.isLt]
    constructor
    · rw [extractionStep_argLabels, hev]
      simp only [rebuildSplit, r, rebuildUIDIndex_live _ hpre,
        dite_eq_left i.isLt]
      funext a
      exact (ancestorStep_split_left _ i x hsplit.1 _).symm
    · simp only [rebuildSplit, r, rebuildUIDIndex_live _ hpre,
        dite_eq_left i.isLt, extractionStep, hev]

end Rhone.Coalescent.SmcPrime
