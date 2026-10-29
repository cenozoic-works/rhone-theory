/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanDeath

/-! # Finite child branches retain the exact chronological UID births and deaths -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem historyClade_of_path (N : ℕ) (ω : EventPath) (k a : ℕ) (hk : k < N) :
    historyClade N (fun j : Fin N => ω j.val) k a =
      Finset.univ.filter (fun i => ancestorLabel N ω leftBoundaryProbe i k = a) := by
  classical
  ext i
  simp only [historyClade, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ancestorLabel_eq_of_prefix N (historyExtension N (fun j : Fin N => ω j.val))
    ω leftBoundaryProbe i k (fun l hl => historyExtension_of_path N ω l (by omega))]

theorem historyChildBranch_of_path_pair (N : ℕ) (ω : EventPath)
    (k : Fin (N - 1)) (ij : ℕ × ℕ)
    (hev : (ω (k.val + 1)).2.2 = .inr (.inl ij)) (hij : ij.1 < ij.2)
    (hj : ij.2 < (ω k.val).1.2.2.1) (right : Bool) :
    historyChildBranch N (fun j : Fin N => ω j.val) k right =
      let a := liveLabelAt (ω k.val).1 (if right then ij.2 else ij.1)
      finiteBranch (historyClade N (fun j : Fin N => ω j.val) k.val a)
        (pairBirthTime ω k.val a) (ω (k.val + 1)).1.1 := by
  have hk0 : k.val < N := by have := k.isLt; omega
  have hk1 : k.val + 1 < N := by have := k.isLt; omega
  have he0 := historyExtension_of_path N ω k.val hk0
  have he1 := historyExtension_of_path N ω (k.val + 1) hk1
  have hb (a : ℕ) := pairBirthTime_eq_of_prefix
    (historyExtension N (fun j : Fin N => ω j.val)) ω k.val a
    (fun l hl => historyExtension_of_path N ω l (by omega))
  simp only [historyChildBranch, he0, he1, hev, hij, hj, and_self, ite_eq_left, hb]

theorem sample_clade_pair_proper (N : ℕ) (s : State) (hs : Valid s)
    (f : Fin N → ℕ) (hf : ∀ k, ∃ a, f a = (s.2.2.2 k).1)
    (i j : Fin s.2.2.1) (hij : i ≠ j) :
    (Finset.univ.filter (fun a => f a = (s.2.2.2 i).1)).Nonempty ∧
      Finset.univ.filter (fun a => f a = (s.2.2.2 i).1) ≠ Finset.univ := by
  classical
  obtain ⟨a, ha⟩ := hf i
  obtain ⟨b, hb⟩ := hf j
  refine ⟨⟨a, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha]⟩, ?_⟩
  intro he
  have hmem : b ∈ Finset.univ.filter (fun a => f a = (s.2.2.2 i).1) := by
    rw [he]
    exact Finset.mem_univ b
  have hbi : f b = (s.2.2.2 i).1 := (Finset.mem_filter.mp hmem).2
  exact hij (hs.2.2.2 (hbi.symm.trans hb))

theorem historyChildBranch_mem_tree (N : ℕ) (h : KingmanHistory N)
    (k : Fin (N - 1)) (right : Bool) :
    ∃ i, (metricTreeFromHistory N h).2 i = historyChildBranch N h k right := by
  have hm : historyChildBranch N h k right ∈
      (List.finRange (N - 1)).flatMap
        (fun j => [historyChildBranch N h j false, historyChildBranch N h j true]) := by
    apply List.mem_flatMap.mpr
    refine ⟨k, by simp, ?_⟩
    cases right <;> simp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  exact ⟨i, hi⟩

theorem metric_tree_branch_from_child (N : ℕ) (h : KingmanHistory N)
    (i : Fin (metricTreeFromHistory N h).1) :
    ∃ k : Fin (N - 1), ∃ right : Bool,
      (metricTreeFromHistory N h).2 i = historyChildBranch N h k right := by
  have hm : (metricTreeFromHistory N h).2 i ∈
      (List.finRange (N - 1)).flatMap
        (fun j => [historyChildBranch N h j false, historyChildBranch N h j true]) :=
    List.get_mem _ i
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with hk | hk
  · exact ⟨k, false, hk⟩
  · exact ⟨k, true, hk⟩

end Rhone.Coalescent.SmcPrime
