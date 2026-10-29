/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanCompletion

/-! # Birth and removal of lineage identifiers under Kingman mergers -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem liveOfList_uid_present (l : List (ℕ × Material)) (a : ℕ) :
    (∃ i, ((liveOfList l).2 i).1 = a) ↔ ∃ p ∈ l, p.1 = a := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨l.get i, List.get_mem l i, hi⟩
  · rintro ⟨p, hp, hpa⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    exact ⟨i, by change (l.get i).1 = a; rw [hi]; exact hpa⟩

theorem coalSuccessor_uid_present (s : State) (hs : Valid s)
    (i j : Fin s.2.2.1) (hij : i.val < j.val) (a : ℕ) :
    (∃ k, ((coalSuccessor s i j).2.2.2 k).1 = a) ↔
      a = s.2.1 ∨ ((∃ k, (s.2.2.2 k).1 = a) ∧
        a ≠ (s.2.2.2 i).1 ∧ a ≠ (s.2.2.2 j).1) := by
  classical
  let l := ((List.finRange s.2.2.1).filter (fun v => v ≠ i ∧ v ≠ j)).map s.2.2.2 ++
    [(s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2)]
  have he : coalSuccessor s i j = (s.1, s.2.1 + 1, liveOfList l) := by
    simp only [coalSuccessor, ite_eq_left hij, l]
  rw [he]
  change (∃ k, ((liveOfList l).2 k).1 = a) ↔ _
  rw [liveOfList_uid_present]
  constructor
  · rintro ⟨p, hp, hpa⟩
    rcases List.mem_append.mp hp with hold | hnew
    · obtain ⟨v, hv, he⟩ := List.mem_map.mp hold
      have hvij : v ≠ i ∧ v ≠ j := by simpa using (List.mem_filter.mp hv).2
      have hva : (s.2.2.2 v).1 = a := (congrArg Prod.fst he).trans hpa
      refine Or.inr ⟨⟨v, hva⟩, ?_, ?_⟩
      · intro hai
        exact hvij.1 (hs.2.2.2 (hva.trans hai))
      · intro haj
        exact hvij.2 (hs.2.2.2 (hva.trans haj))
    · have he : p = (s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2) := by
        simpa only [List.mem_singleton] using hnew
      exact Or.inl (hpa.symm.trans (congrArg Prod.fst he))
  · rintro (ha | ⟨⟨v, hva⟩, hai, haj⟩)
    · refine ⟨(s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2), ?_, ha.symm⟩
      exact List.mem_append.mpr (Or.inr (by simp))
    · have hvi : v ≠ i := by intro h; subst v; exact hai hva.symm
      have hvj : v ≠ j := by intro h; subst v; exact haj hva.symm
      refine ⟨s.2.2.2 v, ?_, hva⟩
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
        ⟨v, by simp [hvi, hvj], rfl⟩))

theorem KingmanTransition.fresh_le {p : AugmentedState × AugmentedState}
    (hp : KingmanTransition p) : p.1.1.2.1 ≤ p.2.1.2.1 := by
  by_cases hm : 2 ≤ p.1.1.2.2.1
  · rw [hp.fresh hm]
    omega
  · obtain ⟨he, _⟩ := (ite_eq_right hm).mp hp
    rw [he]

theorem KingmanTransition.uid_present_backward {p : AugmentedState × AugmentedState}
    (hp : KingmanTransition p) (hs : Valid p.1.1) (a : ℕ) (ha : a < p.1.1.2.1)
    (hn : ∃ i, (p.2.1.2.2.2 i).1 = a) : ∃ i, (p.1.1.2.2.2 i).1 = a := by
  classical
  by_cases hm : 2 ≤ p.1.1.2.2.1
  · obtain ⟨ij, hij, hj, _, he, _⟩ := (ite_eq_left hm).mp hp
    have hi : ij.1 < p.1.1.2.2.1 := lt_trans hij hj
    have he' : p.2.1 = atTime p.2.1.1 (coalSuccessor p.1.1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩) := by
      simpa only [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using he
    rw [he'] at hn
    change ∃ i, ((coalSuccessor p.1.1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩).2.2.2 i).1 = a at hn
    rcases (coalSuccessor_uid_present p.1.1 hs ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ hij a).mp hn with
      hnew | ⟨hold, _, _⟩
    · omega
    · exact hold
  · obtain ⟨he, _⟩ := (ite_eq_right hm).mp hp
    change p.2.1 = p.1.1 at he
    rw [he] at hn
    exact hn

theorem kingman_uid_present_earlier (ω : EventPath)
    (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k l a : ℕ)
    (hkl : k ≤ l) (ha : a < (ω k).1.2.1)
    (hn : ∃ i, ((ω l).1.2.2.2 i).1 = a) :
    ∃ i, ((ω k).1.2.2.2 i).1 = a := by
  have hf : Monotone (fun j => (ω j).1.2.1) :=
    monotone_nat_of_le_succ (fun j => (hstep j).fresh_le)
  induction l with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    exact hn
  | succ l ih =>
    by_cases he : k = l + 1
    · subst k
      exact hn
    · have hkl' : k ≤ l := by omega
      have ha' : a < (ω l).1.2.1 := lt_of_lt_of_le ha (hf hkl')
      exact ih hkl' ((hstep l).uid_present_backward (hvalid l) a ha' hn)

theorem KingmanTransition.sample_old_iff {p : AugmentedState × AugmentedState}
    (hp : KingmanTransition p) (hs : Valid p.1.1) (a : ℕ) (ha : a < p.1.1.2.1)
    (hn : ∃ i, (p.2.1.2.2.2 i).1 = a) (b : ℕ) :
    ancestorStep p.1.1 p.2.2.2 leftBoundaryProbe b = a ↔ b = a := by
  classical
  by_cases hm : 2 ≤ p.1.1.2.2.1
  · obtain ⟨ij, hij, hj, hev, he, _⟩ := (ite_eq_left hm).mp hp
    have hi : ij.1 < p.1.1.2.2.1 := lt_trans hij hj
    change p.2.2.2 = .inr (.inl ij) at hev
    have he' : p.2.1 = atTime p.2.1.1 (coalSuccessor p.1.1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩) := by
      simpa only [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using he
    rw [he'] at hn
    change ∃ i, ((coalSuccessor p.1.1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩).2.2.2 i).1 = a at hn
    have hold : (∃ k, (p.1.1.2.2.2 k).1 = a) ∧
        a ≠ (p.1.1.2.2.2 ⟨ij.1, hi⟩).1 ∧ a ≠ (p.1.1.2.2.2 ⟨ij.2, hj⟩).1 := by
      rcases (coalSuccessor_uid_present p.1.1 hs ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ hij a).mp hn with
        hnew | hold
      · omega
      · exact hold
    have hli : liveLabelAt p.1.1 ij.1 = (p.1.1.2.2.2 ⟨ij.1, hi⟩).1 := by
      simp only [liveLabelAt, dite_eq_left hi]
    have hlj : liveLabelAt p.1.1 ij.2 = (p.1.1.2.2.2 ⟨ij.2, hj⟩).1 := by
      simp only [liveLabelAt, dite_eq_left hj]
    simp only [ancestorStep, hev, hij, hj, and_self, ite_eq_left, hli, hlj]
    by_cases hhit : b = (p.1.1.2.2.2 ⟨ij.1, hi⟩).1 ∨
        b = (p.1.1.2.2.2 ⟨ij.2, hj⟩).1
    · have hba : b ≠ a := by
        intro h
        subst b
        rcases hhit with h | h
        · exact hold.2.1 h
        · exact hold.2.2 h
      simp only [ite_eq_left hhit, ne_of_gt ha, hba]
    · rw [ite_eq_right hhit]
  · obtain ⟨_, hev⟩ := (ite_eq_right hm).mp hp
    change p.2.2.2 = .inl () at hev
    simp only [hev, ancestorStep]

theorem kingman_sample_descendants_persist (N : ℕ) (ω : EventPath)
    (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k l a : ℕ)
    (hkl : k ≤ l) (ha : a < (ω k).1.2.1)
    (hn : ∃ v, ((ω l).1.2.2.2 v).1 = a) (i : Fin N) :
    ancestorLabel N ω leftBoundaryProbe i l = a ↔
      ancestorLabel N ω leftBoundaryProbe i k = a := by
  have hf : Monotone (fun j => (ω j).1.2.1) :=
    monotone_nat_of_le_succ (fun j => (hstep j).fresh_le)
  induction l with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    rfl
  | succ l ih =>
    by_cases he : k = l + 1
    · subst k
      rfl
    · have hkl' : k ≤ l := by omega
      have ha' : a < (ω l).1.2.1 := lt_of_lt_of_le ha (hf hkl')
      have hold := (hstep l).uid_present_backward (hvalid l) a ha' hn
      exact ((hstep l).sample_old_iff (hvalid l) a ha' hn
        (ancestorLabel N ω leftBoundaryProbe i l)).trans (ih hkl' hold)

end Rhone.Coalescent.SmcPrime
