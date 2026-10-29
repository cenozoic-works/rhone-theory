/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitLeftInventorySuccessors

/-! # Old pair extraction succeeds through lineage identifier and sample lookups -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem ExtractionInventory.parent_lookup {N : ℕ} {z : OneSplitExtractionState N}
    {s : State} (h : ExtractionInventory z s) (i : Fin s.2.2.1)
    (hi : z.detached ≠ some (s.2.2.2 i).1) :
    ∃ u : Fin N, ∃ v : Fin z.old.1.2.2.1,
      z.argLabels u = (s.2.2.2 i).1 ∧
      z.oldLabels u = (z.old.1.2.2.2 v).1 ∧
      rebuildSampleUID z.oldLabels (extractionClade z.argLabels (s.2.2.2 i).1) =
        (z.old.1.2.2.2 v).1 := by
  obtain ⟨u, hu⟩ := h.2.1.clade_nonempty i hi
  have hup : z.argLabels u = (s.2.2.2 i).1 := (Finset.mem_filter.mp hu).2
  obtain ⟨v, hv⟩ := h.2.2.1 u
  refine ⟨u, v, hup, hv.symm, ?_⟩
  apply rebuildSampleUID_eq
  · exact ⟨u, hu⟩
  · intro a ha
    have hfu : z.argLabels a = z.argLabels u :=
      (Finset.mem_filter.mp ha).2.trans hup.symm
    exact ((h.2.2.2.2 a u).mp hfu).trans hv.symm

theorem extractionStep_old_pair {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (h : ExtractionInventory z pre.1) (hs : Valid pre.1)
    (i j : Fin pre.1.2.2.1) (hij : i.val < j.val)
    (hev : next.2.2 = .inr (.inl (i.val, j.val)))
    (hi : z.detached ≠ some (pre.1.2.2.2 i).1)
    (hj : z.detached ≠ some (pre.1.2.2.2 j).1) :
    ∃ u v : Fin z.old.1.2.2.1, u.val < v.val ∧
      (extractionStep z pre next).old =
        (atTime next.1.1 (coalSuccessor z.old.1 u v),
          (next.1.1, .inr (.inl (u.val, v.val)))) ∧
      (extractionStep z pre next).oldLabels =
        fun a => ancestorStep z.old.1 (.inr (.inl (u.val, v.val)))
          leftBoundaryProbe (z.oldLabels a) := by
  classical
  obtain ⟨a, u, haf, hag, hlu⟩ := h.parent_lookup i hi
  obtain ⟨b, v, hbf, hbg, hlv⟩ := h.parent_lookup j hj
  have hnephys : (pre.1.2.2.2 i).1 ≠ (pre.1.2.2.2 j).1 := by
    intro he
    exact (ne_of_lt hij) (congrArg Fin.val (hs.2.2.2 he))
  have hneold : u ≠ v := by
    intro he
    have hge : z.oldLabels a = z.oldLabels b := hag.trans ((congrArg
      (fun k => (z.old.1.2.2.2 k).1) he).trans hbg.symm)
    have hfe := (h.2.2.2.2 a b).mpr hge
    exact hnephys (haf.symm.trans (hfe.trans hbf))
  have hluval : liveLabelAt pre.1 i.val = (pre.1.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  have hlvval : liveLabelAt pre.1 j.val = (pre.1.2.2.2 j).1 := by
    simp only [liveLabelAt, dite_eq_left j.isLt]
  have hnattach : ¬ ∃ d, z.detached = some d ∧
      (d = (pre.1.2.2.2 i).1 ∨ d = (pre.1.2.2.2 j).1) := by
    rintro ⟨d, hd, hdi | hdj⟩
    · exact hi (hd.trans (congrArg some hdi))
    · exact hj (hd.trans (congrArg some hdj))
  have huvi : u.val ≠ v.val := fun he => hneold (Fin.ext he)
  have hswap {M : ℕ} (r : RebuildState M) (t : ℝ) (a b : ℕ) :
      rebuildCoal r t a b = rebuildCoal r t b a := by
    simp only [rebuildCoal, min_comm, max_comm]
  let r : RebuildState N := (z.old, z.oldLabels, z.oldLabels, none)
  have hfields : (extractionStep z pre next).old =
      (rebuildCoal r next.1.1 (z.old.1.2.2.2 u).1 (z.old.1.2.2.2 v).1).1 ∧
      (extractionStep z pre next).oldLabels =
      (rebuildCoal r next.1.1 (z.old.1.2.2.2 u).1 (z.old.1.2.2.2 v).1).2.1 := by
    simp only [extractionStep, hev, hluval, hlvval, ite_eq_right hnattach, hlu, hlv]
    exact ⟨rfl, rfl⟩
  rcases lt_or_gt_of_ne huvi with huv | hvu
  · refine ⟨u, v, huv, hfields.1.trans
      (rebuildCoal_live r h.1 next.1.1 u v huv), ?_⟩
    rw [hfields.2]
    simp only [rebuildCoal, r, rebuildUIDIndex_live z.old.1 h.1,
      min_eq_left huv.le, max_eq_right huv.le]
  · refine ⟨v, u, hvu, ?_, ?_⟩
    · rw [hfields.1, hswap]
      exact rebuildCoal_live r h.1 next.1.1 v u hvu
    · rw [hfields.2, hswap]
      simp only [rebuildCoal, r, rebuildUIDIndex_live z.old.1 h.1,
        min_eq_left hvu.le, max_eq_right hvu.le]

theorem rebuildCoal_sample_labels {N : ℕ} (z : RebuildState N) (hz : Valid z.1.1)
    (t : ℝ) (i j : Fin z.1.1.2.2.1) (hne : i ≠ j) :
    (rebuildCoal z t (z.1.1.2.2.2 i).1 (z.1.1.2.2.2 j).1).2.1 =
      fun a => if z.2.1 a = (z.1.1.2.2.2 i).1 ∨ z.2.1 a = (z.1.1.2.2.2 j).1
        then z.1.1.2.1 else z.2.1 a := by
  have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hneval with hij | hji
  · simp only [rebuildCoal, rebuildUIDIndex_live z.1.1 hz,
      min_eq_left hij.le, max_eq_right hij.le, ancestorStep_pair_labels z.1.1 i j hij]
  · simp only [rebuildCoal, rebuildUIDIndex_live z.1.1 hz,
      min_eq_right hji.le, max_eq_left hji.le, ancestorStep_pair_labels z.1.1 j i hji,
      or_comm]

end Rhone.Coalescent.SmcPrime
