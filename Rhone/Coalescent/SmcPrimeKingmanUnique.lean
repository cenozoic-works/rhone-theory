/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanChronology
public import Rhone.Coalescent.SmcPrimeActiveUnique

/-! # Child deaths and injectivity of the branch array in Kingman initialization -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem kingman_child_uid_dies (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1)))
    (m : Fin (N - 1)) (r : Bool) (a : ℕ)
    (hdata : (historyChildBranch N (fun j : Fin N => ω j.val) m r).1 =
      historyClade N (fun j : Fin N => ω j.val) m.val a) :
    ¬ (∃ v, ((ω (m.val + 1)).1.2.2.2 v).1 = a) := by
  classical
  have hc := kingman_path_count N ω hinit hstep m.val (by have := m.isLt; omega)
  have hm : 2 ≤ (ω m.val).1.2.2.1 := by have := m.isLt; omega
  obtain ⟨ij, hij, hj, hev, he, _⟩ := (ite_eq_left hm).mp (hstep m.val)
  change ij.2 < (ω m.val).1.2.2.1 at hj
  change (ω (m.val + 1)).2.2 = .inr (.inl ij) at hev
  have hi : ij.1 < (ω m.val).1.2.2.1 := lt_trans hij hj
  let v : Fin (ω m.val).1.2.2.1 := if r then ⟨ij.2, hj⟩ else ⟨ij.1, hi⟩
  let b := ((ω m.val).1.2.2.2 v).1
  have hlabel : liveLabelAt (ω m.val).1 (if r then ij.2 else ij.1) = b := by
    cases r <;> simp only [v, b, Bool.false_eq_true, ite_false, ite_true, liveLabelAt,
      dite_eq_left hi, dite_eq_left hj]
  have hechild := historyChildBranch_of_path_pair N ω m ij hev hij hj r
  rw [hlabel] at hechild
  have hcl : historyClade N (fun j : Fin N => ω j.val) m.val b =
      historyClade N (fun j : Fin N => ω j.val) m.val a := by
    rw [hechild] at hdata
    exact hdata
  obtain ⟨j, hjb⟩ := kingman_path_sample_surjective N ω hinit hvalid hstep m.val v
  have hba : b = a := by
    have hjmem : j ∈ historyClade N (fun j : Fin N => ω j.val) m.val b := by
      rw [historyClade_of_path N ω m.val b (by have := m.isLt; omega)]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjb⟩
    rw [hcl, historyClade_of_path N ω m.val a (by have := m.isLt; omega)] at hjmem
    exact hjb.symm.trans (Finset.mem_filter.mp hjmem).2
  have he' : (ω (m.val + 1)).1 = atTime (ω (m.val + 1)).1.1
      (coalSuccessor (ω m.val).1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩) := by
    simpa only [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using he
  intro hn
  rw [he'] at hn
  rcases (coalSuccessor_uid_present (ω m.val).1 (hvalid m.val)
    ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ hij a).mp hn with hnew | ⟨_, hni, hnj⟩
  · have haf := (hvalid m.val).2.2.1 v
    change b < (ω m.val).1.2.1 at haf
    omega
  · cases r
    · exact hni hba.symm
    · exact hnj hba.symm

theorem kingman_child_injective (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1)))
    (m l : Fin (N - 1)) (r s : Bool)
    (he : historyChildBranch N (fun j : Fin N => ω j.val) m r =
      historyChildBranch N (fun j : Fin N => ω j.val) l s) : m = l ∧ r = s := by
  classical
  have hm := (history_child_branch_positive N ω hinit hvalid hstep m r).2.2
  have hl := (history_child_branch_positive N ω hinit hvalid hstep l s).2.2
  have htimes : (ω (m.val + 1)).1.1 = (ω (l.val + 1)).1.1 := by
    rw [← hm, he, hl]
  have hml : m = l := by
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have ht := kingman_path_time_strict N ω hinit hstep (m.val + 1) (l.val + 1)
        (by omega) (by have := l.isLt; omega)
      exact (ne_of_lt ht) htimes
    · have ht := kingman_path_time_strict N ω hinit hstep (l.val + 1) (m.val + 1)
        (by omega) (by have := m.isLt; omega)
      exact (ne_of_lt ht) htimes.symm
  subst l
  refine ⟨rfl, ?_⟩
  have hmcount := kingman_path_count N ω hinit hstep m.val (by have := m.isLt; omega)
  have hcount : 2 ≤ (ω m.val).1.2.2.1 := by have := m.isLt; omega
  obtain ⟨ij, hij, hj, hev, _, _⟩ := (ite_eq_left hcount).mp (hstep m.val)
  change ij.2 < (ω m.val).1.2.2.1 at hj
  change (ω (m.val + 1)).2.2 = .inr (.inl ij) at hev
  have hi : ij.1 < (ω m.val).1.2.2.1 := lt_trans hij hj
  have hec := congrArg Prod.fst he
  rw [historyChildBranch_of_path_pair N ω m ij hev hij hj r,
    historyChildBranch_of_path_pair N ω m ij hev hij hj s] at hec
  change historyClade N (fun j : Fin N => ω j.val) m.val
      (liveLabelAt (ω m.val).1 (if r then ij.2 else ij.1)) =
    historyClade N (fun j : Fin N => ω j.val) m.val
      (liveLabelAt (ω m.val).1 (if s then ij.2 else ij.1)) at hec
  have hne : (⟨ij.1, hi⟩ : Fin (ω m.val).1.2.2.1) ≠ ⟨ij.2, hj⟩ := by
    intro h
    exact (ne_of_lt hij) (congrArg Fin.val h)
  have hneq : liveLabelAt (ω m.val).1 ij.1 ≠ liveLabelAt (ω m.val).1 ij.2 := by
    simp only [liveLabelAt, dite_eq_left hi, dite_eq_left hj]
    exact fun h => hne ((hvalid m.val).2.2.2 h)
  have hfalse : historyChildBranch N (fun j : Fin N => ω j.val) m false ≠
      historyChildBranch N (fun j : Fin N => ω j.val) m true := by
    intro hb
    have hh := congrArg Prod.fst hb
    rw [historyChildBranch_of_path_pair N ω m ij hev hij hj false,
      historyChildBranch_of_path_pair N ω m ij hev hij hj true] at hh
    change historyClade N (fun j : Fin N => ω j.val) m.val
        (liveLabelAt (ω m.val).1 ij.1) =
      historyClade N (fun j : Fin N => ω j.val) m.val (liveLabelAt (ω m.val).1 ij.2) at hh
    have hd := historyClade_disjoint N (fun j : Fin N => ω j.val) m.val _ _ hneq
    have hp := (history_child_branch_positive N ω hinit hvalid hstep m false).1
    have hnon : (historyChildBranch N (fun j : Fin N => ω j.val) m false).1 ≠ ∅ := by
      intro hz
      simp only [branchLength, hz, true_or, ite_true, lt_self_iff_false] at hp
    have hempty : historyClade N (fun j : Fin N => ω j.val) m.val
        (liveLabelAt (ω m.val).1 ij.1) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      apply Finset.disjoint_left.mp hd hi
      rwa [← hh]
    apply hnon
    rw [historyChildBranch_of_path_pair N ω m ij hev hij hj false]
    exact hempty
  cases r <;> cases s
  · rfl
  · exact False.elim (hfalse he)
  · exact False.elim (hfalse he.symm)
  · rfl

theorem kingman_tree_branch_injective (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) :
    Function.Injective (metricTreeFromHistory N (fun j : Fin N => ω j.val)).2 := by
  classical
  let f := fun m : Fin (N - 1) =>
    [historyChildBranch N (fun j : Fin N => ω j.val) m false,
      historyChildBranch N (fun j : Fin N => ω j.val) m true]
  have hnodup : ((List.finRange (N - 1)).flatMap f).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨?_, ?_⟩
    · intro m _
      have hn : historyChildBranch N (fun j : Fin N => ω j.val) m false ≠
          historyChildBranch N (fun j : Fin N => ω j.val) m true := by
        intro h
        have hh := (kingman_child_injective N ω hinit hvalid hstep m m false true h).2
        cases hh
      simp [f, hn]
    · apply (List.nodup_finRange (N - 1)).imp
      intro m l hml
      apply List.disjoint_left.mpr
      intro b hb hc
      simp only [f, List.mem_cons, List.not_mem_nil, or_false] at hb hc
      rcases hb with hb | hb <;> rcases hc with hc | hc
      all_goals exact hml (kingman_child_injective N ω hinit hvalid hstep m l _ _
        (hb.symm.trans hc)).1
  intro i j he
  exact hnodup.get_inj_iff.mp he

end Rhone.Coalescent.SmcPrime
