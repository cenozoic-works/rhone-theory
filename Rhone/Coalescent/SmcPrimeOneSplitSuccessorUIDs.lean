/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtraction

/-! # Split UID inventories and pair or left-daughter sample updates -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem splitSuccessor_uid_present (s : State) (hs : Valid s)
    (i : Fin s.2.2.1) (x : ℝ) (a : ℕ) :
    (∃ k, ((splitSuccessor s i x).2.2.2 k).1 = a) ↔
      a = s.2.1 ∨ a = s.2.1 + 1 ∨
        ((∃ k, (s.2.2.2 k).1 = a) ∧ a ≠ (s.2.2.2 i).1) := by
  classical
  let l := ((List.finRange s.2.2.1).filter (fun k => k ≠ i)).map s.2.2.2 ++
    [(s.2.1, (splitMaterial (s.2.2.2 i).2 x).1),
      (s.2.1 + 1, (splitMaterial (s.2.2.2 i).2 x).2)]
  change (∃ k, ((liveOfList l).2 k).1 = a) ↔ _
  rw [liveOfList_uid_present]
  constructor
  · rintro ⟨p, hp, hpa⟩
    rcases List.mem_append.mp hp with hold | hnew
    · obtain ⟨k, hk, he⟩ := List.mem_map.mp hold
      have hki : k ≠ i := by simpa using (List.mem_filter.mp hk).2
      have hka : (s.2.2.2 k).1 = a := (congrArg Prod.fst he).trans hpa
      refine Or.inr (Or.inr ⟨⟨k, hka⟩, ?_⟩)
      intro hai
      exact hki (hs.2.2.2 (hka.trans hai))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
      rcases hnew with he | he
      · exact Or.inl (hpa.symm.trans (congrArg Prod.fst he))
      · exact Or.inr (Or.inl (hpa.symm.trans (congrArg Prod.fst he)))
  · rintro (ha | ha | ⟨⟨k, hk⟩, hai⟩)
    · exact ⟨_, List.mem_append.mpr (Or.inr (List.mem_cons_self)), ha.symm⟩
    · exact ⟨(s.2.1 + 1, (splitMaterial (s.2.2.2 i).2 x).2),
        List.mem_append.mpr (Or.inr (by simp)), ha.symm⟩
    · have hki : k ≠ i := by intro h; subst k; exact hai hk.symm
      exact ⟨s.2.2.2 k, List.mem_append.mpr
        (Or.inl (List.mem_map.mpr ⟨k, by simp [hki], rfl⟩)), hk⟩

theorem ancestorStep_pair_labels (s : State) (i j : Fin s.2.2.1)
    (hij : i.val < j.val) (q : GenomicProbe) (a : ℕ) :
    ancestorStep s (.inr (.inl (i.val, j.val))) q a =
      if a = (s.2.2.2 i).1 ∨ a = (s.2.2.2 j).1 then s.2.1 else a := by
  have hi : liveLabelAt s i.val = (s.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  have hj : liveLabelAt s j.val = (s.2.2.2 j).1 := by
    simp only [liveLabelAt, dite_eq_left j.isLt]
  simp only [ancestorStep, hij, j.isLt, and_self, ite_eq_left, hi, hj]

theorem ancestorStep_split_left (s : State) (i : Fin s.2.2.1) (x : ℝ)
    (hx : 0 < x) (a : ℕ) :
    ancestorStep s (.inr (.inr (i.val, x))) leftBoundaryProbe a =
      if a = (s.2.2.2 i).1 then s.2.1 else a := by
  have hprobe : (leftBoundaryProbe.val : ℝ) < x := by
    simpa only [leftBoundaryProbe, Rat.cast_zero] using hx
  have hi : liveLabelAt s i.val = (s.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  simp only [ancestorStep, i.isLt, true_and, hi, hprobe, ite_true]

end Rhone.Coalescent.SmcPrime
