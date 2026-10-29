/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanBranchGeometry
public import Rhone.Coalescent.SmcPrimeTreeChronology

/-! # Lineage identifier birth and child inventory in Kingman initialization -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem kingman_sample_present (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (i : Fin N) (k : ℕ) :
    ∃ v, ((ω k).1.2.2.2 v).1 = ancestorLabel N ω leftBoundaryProbe i k := by
  have hc : ancestorCarried (ω k).1 (leftBoundaryProbe.val : ℝ)
      (ancestorLabel N ω leftBoundaryProbe i k) := by
    induction k with
    | zero => rw [hinit]; exact initial_ancestorCarried N leftBoundaryProbe i
    | succ k ih =>
      by_cases hm : 2 ≤ (ω k).1.2.2.1
      · obtain ⟨ij, hij, hj, hev, he, _⟩ := (ite_eq_left hm).mp (hstep k)
        have hi : ij.1 < (ω k).1.2.2.1 := lt_trans hij hj
        have he' : (ω (k + 1)).1 = atTime (ω (k + 1)).1.1
            (coalSuccessor (ω k).1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩) := by
          simpa only [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using he
        change (ω (k + 1)).2.2 = .inr (.inl ij) at hev
        rw [he']
        simpa only [ancestorLabel, hev, ancestorCarried_atTime] using
          coalSuccessor_ancestorCarried (ω k).1 (hvalid k) leftBoundaryProbe _ ih
            ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ hij
      · obtain ⟨he, hev⟩ := (ite_eq_right hm).mp (hstep k)
        change (ω (k + 1)).2.2 = .inl () at hev
        change (ω (k + 1)).1 = (ω k).1 at he
        simpa only [ancestorLabel, hev, ancestorStep, he] using ih
  obtain ⟨v, hv, _⟩ := hc
  exact ⟨v, hv⟩

theorem kingman_child_data (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (m : Fin (N - 1)) (r : Bool) :
    ∃ a, (∃ v, ((ω m.val).1.2.2.2 v).1 = a) ∧
      historyChildBranch N (fun j : Fin N => ω j.val) m r =
        (historyClade N (fun j : Fin N => ω j.val) m.val a,
          pairBirthTime ω m.val a, (ω (m.val + 1)).1.1) := by
  classical
  have hc := kingman_path_count N ω hinit hstep m.val (by have := m.isLt; omega)
  have hm : 2 ≤ (ω m.val).1.2.2.1 := by have := m.isLt; omega
  obtain ⟨ij, hij, hj, hev, _, _⟩ := (ite_eq_left hm).mp (hstep m.val)
  change ij.2 < (ω m.val).1.2.2.1 at hj
  change (ω (m.val + 1)).2.2 = .inr (.inl ij) at hev
  have hi : ij.1 < (ω m.val).1.2.2.1 := lt_trans hij hj
  let v : Fin (ω m.val).1.2.2.1 := if r then ⟨ij.2, hj⟩ else ⟨ij.1, hi⟩
  let a := ((ω m.val).1.2.2.2 v).1
  have hlabel : liveLabelAt (ω m.val).1 (if r then ij.2 else ij.1) = a := by
    cases r <;> simp only [v, a, Bool.false_eq_true, ite_false, ite_true, liveLabelAt,
      dite_eq_left hi, dite_eq_left hj]
  have he := historyChildBranch_of_path_pair N ω m ij hev hij hj r
  rw [hlabel] at he
  have hp := (history_child_branch_positive N ω hinit hvalid hstep m r).1
  rw [he] at hp
  have hproper : ¬ (historyClade N (fun j : Fin N => ω j.val) m.val a = ∅ ∨
      historyClade N (fun j : Fin N => ω j.val) m.val a = Finset.univ) := by
    intro h
    simp only [finiteBranch, h, ite_true, branchLength, ite_true, lt_self_iff_false] at hp
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hb := pair_birth_time_le_current_time ω (hvalid 0).1 hmono m.val a
  have ht := kingman_path_time_strict_next N ω hinit hstep m.val (by have := m.isLt; omega)
  refine ⟨a, ⟨v, rfl⟩, ?_⟩
  simpa only [finiteBranch, hproper, ite_false, max_eq_right (hb.trans ht.le)] using he

theorem kingman_birth_persist (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k m a : ℕ)
    (hkm : k ≤ m) (hm : m < N) (ha : a < N + k) :
    pairBirthTime ω m a = pairBirthTime ω k a := by
  rw [kingman_pair_birth_time N ω hinit hstep m a hm,
    kingman_pair_birth_time N ω hinit hstep k a (by omega)]
  have hh : (N ≤ a ∧ a < N + m) ↔ (N ≤ a ∧ a < N + k) := by omega
  simp only [hh]

theorem kingman_live_child (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k a : ℕ) (hk : k < N - 1)
    (ha : ∃ v, ((ω k).1.2.2.2 v).1 = a) :
    ∃ m : Fin (N - 1), ∃ r : Bool, k ≤ m.val ∧
      historyChildBranch N (fun j : Fin N => ω j.val) m r =
        (historyClade N (fun j : Fin N => ω j.val) k a,
          pairBirthTime ω k a, (ω (m.val + 1)).1.1) := by
  classical
  obtain ⟨m, hkm, hm, ij, hev, hij, hj, hhit⟩ :=
    kingman_uid_death_parent N ω hinit hvalid hstep k a hk ha
  have hi : ij.1 < (ω m).1.2.2.1 := lt_trans hij hj
  have haf : a < (ω k).1.2.1 := by
    obtain ⟨v, hv⟩ := ha
    rw [← hv]
    exact (hvalid k).2.2.1 v
  have hpres : ∃ v, ((ω m).1.2.2.2 v).1 = a := by
    rcases hhit with h | h
    · exact ⟨⟨ij.1, hi⟩, by simpa only [liveLabelAt, dite_eq_left hi] using h⟩
    · exact ⟨⟨ij.2, hj⟩, by simpa only [liveLabelAt, dite_eq_left hj] using h⟩
  have hcl : historyClade N (fun j : Fin N => ω j.val) m a =
      historyClade N (fun j : Fin N => ω j.val) k a := by
    rw [historyClade_of_path N ω m a (by omega), historyClade_of_path N ω k a (by omega)]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact kingman_sample_descendants_persist N ω hvalid hstep k m a hkm haf hpres i
  have hbirth := kingman_birth_persist N ω hinit hstep k m a hkm (by omega)
    (by rw [kingman_path_fresh N ω hinit hstep k (by omega)] at haf; exact haf)
  let mm : Fin (N - 1) := ⟨m, hm⟩
  have hraw (r : Bool) (hr : liveLabelAt (ω m).1 (if r then ij.2 else ij.1) = a) :
      historyChildBranch N (fun j : Fin N => ω j.val) mm r =
        (historyClade N (fun j : Fin N => ω j.val) k a, pairBirthTime ω k a,
          (ω (m + 1)).1.1) := by
    have he := historyChildBranch_of_path_pair N ω mm ij hev hij hj r
    rw [hr] at he
    have hp := (history_child_branch_positive N ω hinit hvalid hstep mm r).1
    rw [he] at hp
    have hproper : ¬ (historyClade N (fun j : Fin N => ω j.val) m a = ∅ ∨
        historyClade N (fun j : Fin N => ω j.val) m a = Finset.univ) := by
      intro h
      simp only [mm, finiteBranch, h, ite_true, branchLength, ite_true,
        lt_self_iff_false] at hp
    have hmono : Monotone (fun k => (ω k).1.1) :=
      monotone_nat_of_le_succ (fun k => (hstep k).time_le)
    have hlo := pair_birth_time_le_current_time ω (hvalid 0).1 hmono m a
    have ht := kingman_path_time_strict_next N ω hinit hstep m (by omega)
    change historyChildBranch N (fun j : Fin N => ω j.val) mm r =
      finiteBranch (historyClade N (fun j : Fin N => ω j.val) m a)
        (pairBirthTime ω m a) (ω (m + 1)).1.1 at he
    simp only [finiteBranch, hproper, ite_false, max_eq_right (hlo.trans ht.le)] at he
    simpa only [hcl, hbirth] using he
  rcases hhit with h | h
  · exact ⟨mm, false, hkm, hraw false h⟩
  · exact ⟨mm, true, hkm, hraw true h⟩

end Rhone.Coalescent.SmcPrime
