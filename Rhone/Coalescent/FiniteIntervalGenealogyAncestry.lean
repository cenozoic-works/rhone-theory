/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalGenealogyMaterial
public import Rhone.Coalescent.SmcSupport.Successors

/-! # Ancestor labels correspond to material carried by the live lineage arrays -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport

def ancestorCarried (s : State) (q : ℝ) (a : ℕ) : Prop :=
  ∃ i, (s.2.2.2 i).1 = a ∧ materialContains (s.2.2.2 i).2 q

theorem liveOfList_ancestor_mem (l : List (ℕ × Material)) (p : ℕ × Material)
    (hp : p ∈ l) (q : ℝ) (hq : materialContains p.2 q) :
    ∃ i, ((liveOfList l).2 i).1 = p.1 ∧ materialContains ((liveOfList l).2 i).2 q := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  refine ⟨i, ?_⟩
  change (l.get i).1 = p.1 ∧ materialContains (l.get i).2 q
  rw [hi]
  exact ⟨rfl, hq⟩

theorem initial_ancestorCarried (N : ℕ) (q : GenomicProbe) (i : Fin N) :
    ancestorCarried (initialState N) (q.val : ℝ) i.val := by
  refine ⟨i, rfl, (initial_materialContains N i _).mpr ?_⟩
  exact ⟨by exact_mod_cast q.property.1, by exact_mod_cast q.property.2⟩

theorem ancestorCarried_atTime (s : State) (t q : ℝ) (a : ℕ) :
    ancestorCarried (atTime t s) q a ↔ ancestorCarried s q a := Iff.rfl

theorem coalSuccessor_ancestorCarried (s : State) (hs : Valid s)
    (q : GenomicProbe) (a : ℕ) (ha : ancestorCarried s (q.val : ℝ) a)
    (i j : Fin s.2.2.1) (hij : i.val < j.val) :
    ancestorCarried (coalSuccessor s i j) (q.val : ℝ)
      (ancestorStep s (.inr (.inl (i.val, j.val))) q a) := by
  obtain ⟨k, hka, hkq⟩ := ha
  have hli : liveLabelAt s i.val = (s.2.2.2 i).1 := by simp [liveLabelAt, i.isLt]
  have hlj : liveLabelAt s j.val = (s.2.2.2 j).1 := by simp [liveLabelAt, j.isLt]
  have hstep : ancestorStep s (.inr (.inl (i.val, j.val))) q a =
      if a = (s.2.2.2 i).1 ∨ a = (s.2.2.2 j).1 then s.2.1 else a := by
    simp only [ancestorStep, hij, j.isLt, and_self, ite_eq_left, hli, hlj]
  rw [hstep]
  unfold coalSuccessor
  rw [ite_eq_left hij]
  dsimp only
  by_cases hhit : a = (s.2.2.2 i).1 ∨ a = (s.2.2.2 j).1
  · rw [ite_eq_left hhit]
    have hm : materialContains (mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2) (q.val : ℝ) := by
      apply (materialContains_merge _ _ _).mpr
      rcases hhit with hi | hj
      · have hki : k = i := hs.2.2.2 (hka.trans hi)
        subst k
        exact Or.inl hkq
      · have hkj : k = j := hs.2.2.2 (hka.trans hj)
        subst k
        exact Or.inr hkq
    exact liveOfList_ancestor_mem _ (s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2)
      (List.mem_append.mpr (Or.inr (by simp))) _ hm
  · rw [ite_eq_right hhit]
    have hki : k ≠ i := by intro h; subst k; exact hhit (Or.inl hka.symm)
    have hkj : k ≠ j := by intro h; subst k; exact hhit (Or.inr hka.symm)
    have hmem : (s.2.2.2 k) ∈
        ((List.finRange s.2.2.1).filter (fun v => v ≠ i ∧ v ≠ j)).map s.2.2.2 ++
          [(s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2)] := by
      apply List.mem_append.mpr
      left
      apply List.mem_map.mpr
      exact ⟨k, by simp [hki, hkj], rfl⟩
    obtain ⟨v, hv, hvq⟩ := liveOfList_ancestor_mem _ _ hmem _ hkq
    exact ⟨v, hv.trans hka, hvq⟩

theorem splitSuccessor_ancestorCarried (s : State) (hs : Valid s)
    (q : GenomicProbe) (a : ℕ) (ha : ancestorCarried s (q.val : ℝ) a)
    (i : Fin s.2.2.1) (x : ℝ) :
    ancestorCarried (splitSuccessor s i x) (q.val : ℝ)
      (ancestorStep s (.inr (.inr (i.val, x))) q a) := by
  obtain ⟨k, hka, hkq⟩ := ha
  have hli : liveLabelAt s i.val = (s.2.2.2 i).1 := by simp [liveLabelAt, i.isLt]
  have hstep : ancestorStep s (.inr (.inr (i.val, x))) q a =
      if a = (s.2.2.2 i).1 then
        if (q.val : ℝ) < x then s.2.1 else s.2.1 + 1
      else a := by
    simp only [ancestorStep, i.isLt, true_and, hli]
  rw [hstep]
  unfold splitSuccessor
  dsimp only
  by_cases hhit : a = (s.2.2.2 i).1
  · rw [ite_eq_left hhit]
    have hki : k = i := hs.2.2.2 (hka.trans hhit)
    subst k
    by_cases hcut : (q.val : ℝ) < x
    · rw [ite_eq_left hcut]
      have hleft : materialContains (splitMaterial (s.2.2.2 i).2 x).1 (q.val : ℝ) :=
        (materialContains_split_left _ _ _).mpr ⟨hkq, hcut⟩
      exact liveOfList_ancestor_mem _ (s.2.1, (splitMaterial (s.2.2.2 i).2 x).1)
        (List.mem_append.mpr (Or.inr (by simp))) _ hleft
    · rw [ite_eq_right hcut]
      have hright : materialContains (splitMaterial (s.2.2.2 i).2 x).2 (q.val : ℝ) :=
        (materialContains_split_right _ _ _).mpr ⟨hkq, le_of_not_gt hcut⟩
      exact liveOfList_ancestor_mem _ (s.2.1 + 1, (splitMaterial (s.2.2.2 i).2 x).2)
        (List.mem_append.mpr (Or.inr (by simp))) _ hright
  · rw [ite_eq_right hhit]
    have hki : k ≠ i := by intro h; subst k; exact hhit hka.symm
    have hmem : s.2.2.2 k ∈
        ((List.finRange s.2.2.1).filter (fun v => v ≠ i)).map s.2.2.2 ++
          [(s.2.1, (splitMaterial (s.2.2.2 i).2 x).1),
            (s.2.1 + 1, (splitMaterial (s.2.2.2 i).2 x).2)] := by
      apply List.mem_append.mpr
      left
      apply List.mem_map.mpr
      exact ⟨k, by simp [hki], rfl⟩
    obtain ⟨v, hv, hvq⟩ := liveOfList_ancestor_mem _ _ hmem _ hkq
    exact ⟨v, hv.trans hka, hvq⟩

end Rhone.Coalescent.IntervalProcess
