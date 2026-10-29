/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitNextOldRecord

/-! # Rebuilding the old pair step from the extracted old pair -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem rebuildCoal_swap {N : ℕ} (r : RebuildState N) (t : ℝ) (a b : ℕ) :
    rebuildCoal r t a b = rebuildCoal r t b a := by
  simp only [rebuildCoal, min_comm, max_comm]

theorem rebuildStep_extracted_old_pair_eq (N : ℕ)
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
      rebuildStep (extractOneSplitSkeleton N h) r (.inl k) =
        rebuildCoal r (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1
          ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 i).1
          ((h ⟨n.val, Finset.mem_Iic.mpr (by have := n.isLt; omega)⟩).1.2.2.2 j).1 := by
  classical
  dsimp only
  let z := extractionRun N h n.val
  let pre := h ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩
  let next := h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩
  let η := extractOneSplitSkeleton N h
  let r : RebuildState N := (pre, z.argLabels, g, z.detached)
  let ro : RebuildState N := (z.old, z.oldLabels, z.oldLabels, none)
  have hinv := extractionRun_inventory N h hs n.val n.isLt.le
  have hvalid := hs.2.1 ⟨n.val, Finset.mem_Iic.mpr n.isLt.le⟩
  obtain ⟨a, u, haf, hag, hlu⟩ := hinv.parent_lookup i hi
  obtain ⟨b, v, hbf, hbg, hlv⟩ := hinv.parent_lookup j hj
  have hne : u ≠ v := by
    intro he
    have hge : z.oldLabels a = z.oldLabels b := by rw [hag, hbg, he]
    have hfe := (hinv.2.2.2.2 a b).mpr hge
    have heij := hvalid.2.2.2 (haf.symm.trans (hfe.trans hbf))
    exact (ne_of_lt hij) (congrArg Fin.val heij)
  have hiuid : liveLabelAt pre.1 i.val = (pre.1.2.2.2 i).1 := by
    have hb : i.val < pre.1.2.2.1 := i.isLt
    simp only [liveLabelAt, dite_eq_left hb]
    rfl
  have hjuid : liveLabelAt pre.1 j.val = (pre.1.2.2.2 j).1 := by
    have hb : j.val < pre.1.2.2.1 := j.isLt
    simp only [liveLabelAt, dite_eq_left hb]
    rfl
  have hnattach : ¬ ∃ d, z.detached = some d ∧
      (d = (pre.1.2.2.2 i).1 ∨ d = (pre.1.2.2.2 j).1) := by
    rintro ⟨d, hd, hdi | hdj⟩
    · exact hi (hd.trans (congrArg some hdi))
    · exact hj (hd.trans (congrArg some hdj))
  dsimp only [z, pre] at hiuid hjuid hnattach
  have hmnext : (extractionRun N h (n.val + 1)).mergers = z.mergers + 1 := by
    rw [extractionRun_succ N h n.val n.isLt]
    simp only [z, extractionStep, hev, hiuid, hjuid, ite_eq_right hnattach]
  have hold : (extractionRun N h (n.val + 1)).old =
      (rebuildCoal ro next.1.1 (z.old.1.2.2.2 u).1 (z.old.1.2.2.2 v).1).1 := by
    rw [extractionRun_succ N h n.val n.isLt]
    simp only [z, next, ro, extractionStep, hev, hiuid, hjuid, ite_eq_right hnattach, hlu, hlv]
  have hp := extractionRun_history_prefix N h hs n.val n.isLt.le
  have hc := (hp.records ⟨z.mergers, hp.bound⟩ le_rfl).2
  rw [hp.current] at hc
  change z.old.1.2.2.1 = N - z.mergers at hc
  have htwo : 2 ≤ z.old.1.2.2.1 := by
    by_contra hn
    have hu : u.val < z.old.1.2.2.1 := u.isLt
    have hv : v.val < z.old.1.2.2.1 := v.isLt
    have he : u.val = v.val := by omega
    exact hne (Fin.ext he)
  have hm : z.mergers < N - 1 := by omega
  let k : Fin (N - 1) := ⟨z.mergers, hm⟩
  have hpre : η.1 ⟨z.mergers, hp.bound⟩ = z.old :=
    extractionRun_final_old_record N h hs n.val n.isLt.le
  have hpost : η.1 ⟨z.mergers + 1, by omega⟩ =
      (rebuildCoal ro next.1.1 (z.old.1.2.2.2 u).1 (z.old.1.2.2.2 v).1).1 := by
    rw [extractionRun_next_old_record N h hs n.val n.isLt hmnext, hold]
  have hclu : historyClade N η.1 z.mergers (z.old.1.2.2.2 u).1 =
      extractionClade z.argLabels (pre.1.2.2.2 i).1 := by
    rw [extractionRun_final_history_clade N h hs n.val n.isLt.le]
    exact hinv.parent_clade a i u haf hag
  have hclv : historyClade N η.1 z.mergers (z.old.1.2.2.2 v).1 =
      extractionClade z.argLabels (pre.1.2.2.2 j).1 := by
    rw [extractionRun_final_history_clade N h hs n.val n.isLt.le]
    exact hinv.parent_clade b j v hbf hbg
  have hfu : rebuildSampleUID z.argLabels
      (extractionClade z.argLabels (pre.1.2.2.2 i).1) = (pre.1.2.2.2 i).1 :=
    hinv.2.1.rebuild_clade i hi
  have hfv : rebuildSampleUID z.argLabels
      (extractionClade z.argLabels (pre.1.2.2.2 j).1) = (pre.1.2.2.2 j).1 :=
    hinv.2.1.rebuild_clade j hj
  have hluold : liveLabelAt z.old.1 u.val = (z.old.1.2.2.2 u).1 := by
    have hb : u.val < z.old.1.2.2.1 := u.isLt
    simp only [liveLabelAt, dite_eq_left hb]
    rfl
  have hlvold : liveLabelAt z.old.1 v.val = (z.old.1.2.2.2 v).1 := by
    have hb : v.val < z.old.1.2.2.1 := v.isLt
    simp only [liveLabelAt, dite_eq_left hb]
    rfl
  refine ⟨k, rfl, ?_⟩
  change rebuildStep η r (.inl k) = rebuildCoal r next.1.1 _ _
  have hneval : u.val ≠ v.val := fun he => hne (Fin.ext he)
  rcases lt_or_gt_of_ne hneval with huv | hvu
  · rw [rebuildCoal_live ro hinv.1 next.1.1 u v huv] at hpost
    simp only [rebuildStep, k, hpre, hpost, rebuildEventTime, hluold, hlvold,
      hclu, hclv, r, hfu, hfv, atTime]
    rfl
  · rw [rebuildCoal_swap ro, rebuildCoal_live ro hinv.1 next.1.1 v u hvu] at hpost
    simp only [rebuildStep, k, hpre, hpost, rebuildEventTime, hluold, hlvold,
      hclu, hclv, r, hfu, hfv, atTime]
    exact rebuildCoal_swap _ _ _ _

end Rhone.Coalescent.SmcPrime
