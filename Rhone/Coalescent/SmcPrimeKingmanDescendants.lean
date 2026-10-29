/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanSupport

/-! # Every live Kingman lineage has a sample descendant -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

theorem coalSuccessor_sample_surjective (N : ℕ) (s : State)
    (hs : Valid s) (f : Fin N → ℕ) (hf : ∀ k, ∃ a, f a = (s.2.2.2 k).1)
    (i j : Fin s.2.2.1) (hij : i.val < j.val) :
    ∀ k, ∃ a, ancestorStep s (.inr (.inl (i.val, j.val)))
      leftBoundaryProbe (f a) = ((coalSuccessor s i j).2.2.2 k).1 := by
  classical
  intro k
  have hli : liveLabelAt s i.val = (s.2.2.2 i).1 := by simp [liveLabelAt, i.isLt]
  have hlj : liveLabelAt s j.val = (s.2.2.2 j).1 := by simp [liveLabelAt, j.isLt]
  have hmem : (coalSuccessor s i j).2.2.2 k ∈
      ((List.finRange s.2.2.1).filter (fun v => v ≠ i ∧ v ≠ j)).map s.2.2.2 ++
        [(s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2)] := by
    generalize hz : coalSuccessor s i j = z at k ⊢
    have hz' : z = (s.1, s.2.1 + 1, liveOfList
        (((List.finRange s.2.2.1).filter (fun v => v ≠ i ∧ v ≠ j)).map s.2.2.2 ++
          [(s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2)])) := by
      rw [← hz]
      simp only [coalSuccessor, ite_eq_left hij]
    clear hz
    subst z
    exact List.get_mem _ k
  rcases List.mem_append.mp hmem with hold | hnew
  · obtain ⟨v, hv, he⟩ := List.mem_map.mp hold
    have hvij : v ≠ i ∧ v ≠ j := by simpa using (List.mem_filter.mp hv).2
    obtain ⟨a, ha⟩ := hf v
    have hni : f a ≠ (s.2.2.2 i).1 := by
      intro h
      exact hvij.1 (hs.2.2.2 (ha.symm.trans h))
    have hnj : f a ≠ (s.2.2.2 j).1 := by
      intro h
      exact hvij.2 (hs.2.2.2 (ha.symm.trans h))
    refine ⟨a, ?_⟩
    simp only [ancestorStep, hij, j.isLt, and_self, ite_eq_left, hli, hlj,
      hni, hnj, false_or]
    exact ha.trans (congrArg Prod.fst he)
  · have he : (coalSuccessor s i j).2.2.2 k =
        (s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2) := by
      simpa only [List.mem_singleton] using hnew
    obtain ⟨a, ha⟩ := hf i
    refine ⟨a, ?_⟩
    rw [he]
    simp only [ancestorStep, hij, j.isLt, and_self, ite_eq_left, hli, hlj,
      ha, true_or]

theorem kingman_path_sample_surjective (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) :
    ∀ v, ∃ a, ancestorLabel N ω leftBoundaryProbe a k = ((ω k).1.2.2.2 v).1 := by
  classical
  induction k with
  | zero =>
    rw [hinit]
    intro v
    exact ⟨v, rfl⟩
  | succ k ih =>
    by_cases hm : 2 ≤ (ω k).1.2.2.1
    · obtain ⟨ij, hij, hj, hev, he, _⟩ := (ite_eq_left hm).mp (hstep k)
      change (ω (k + 1)).2.2 = .inr (.inl ij) at hev
      have hi : ij.1 < (ω k).1.2.2.1 := lt_trans hij hj
      have he' : (ω (k + 1)).1 =
          atTime (ω (k + 1)).1.1 (coalSuccessor (ω k).1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩) := by
        simpa only [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using he
      rw [he']
      intro v
      obtain ⟨a, ha⟩ := coalSuccessor_sample_surjective N (ω k).1 (hvalid k)
        (fun a => ancestorLabel N ω leftBoundaryProbe a k) ih ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ hij v
      exact ⟨a, by simpa only [ancestorLabel, hev, atTime] using ha⟩
    · obtain ⟨he, hev⟩ := (ite_eq_right hm).mp (hstep k)
      change (ω (k + 1)).2.2 = .inl () at hev
      rw [he]
      intro v
      obtain ⟨a, ha⟩ := ih v
      exact ⟨a, by simpa only [ancestorLabel, hev, ancestorStep] using ha⟩

theorem eventProcess_kingman_sample_surjective (N : ℕ) :
    ∀ᵐ ω ∂(eventProcess false 0).pathLaw (initialState N, (0, .inl ())),
      ∀ k v, ∃ a, ancestorLabel N ω leftBoundaryProbe a k = ((ω k).1.2.2.2 v).1 := by
  filter_upwards [eventProcess_chronologicalAncestryPath N false 0,
    eventProcess_kingmanTransition (initialState N, (0, .inl ()))] with ω hc hs
  exact kingman_path_sample_surjective N ω (congrArg Prod.fst hc.1)
    (fun k => hc.valid k) hs

theorem historyClade_disjoint (N : ℕ) (h : KingmanHistory N) (k a b : ℕ)
    (hab : a ≠ b) : Disjoint (historyClade N h k a) (historyClade N h k b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [historyClade, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hab (hi.symm.trans hj)

theorem historyClade_nonempty (N : ℕ) (h : KingmanHistory N) (k a : ℕ) :
    (historyClade N h k a).Nonempty ↔
      ∃ i, ancestorLabel N (historyExtension N h) leftBoundaryProbe i k = a := by
  classical
  simp only [Finset.nonempty_iff_ne_empty, ne_eq]
  simp [historyClade, Finset.filter_eq_empty_iff]

end Rhone.Coalescent.SmcPrime
