/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanBranches
public import Rhone.Coalescent.SmcPrimeKingmanNonnegative

/-! # Pair-child branches of Kingman histories have positive length and exact death times -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem history_child_branch_positive (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hvalid : ∀ k, Valid (ω k).1)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : Fin (N - 1)) (right : Bool) :
    let b := historyChildBranch N (fun j : Fin N => ω j.val) k right
    0 < branchLength b ∧ b.2.1 ≤ (ω k.val).1.1 ∧ b.2.2 = (ω (k.val + 1)).1.1 := by
  classical
  have hk : k.val + 1 < N := by have := k.isLt; omega
  have hc := kingman_path_count N ω hinit hstep k.val (by omega)
  have hm : 2 ≤ (ω k.val).1.2.2.1 := by omega
  obtain ⟨ij, hij, hj, hev, _, _⟩ := (ite_eq_left hm).mp (hstep k.val)
  change ij.2 < (ω k.val).1.2.2.1 at hj
  change (ω (k.val + 1)).2.2 = .inr (.inl ij) at hev
  have hi : ij.1 < (ω k.val).1.2.2.1 := lt_trans hij hj
  let i : Fin (ω k.val).1.2.2.1 := if right then ⟨ij.2, hj⟩ else ⟨ij.1, hi⟩
  let j : Fin (ω k.val).1.2.2.1 := if right then ⟨ij.1, hi⟩ else ⟨ij.2, hj⟩
  have hne0 : (⟨ij.1, hi⟩ : Fin (ω k.val).1.2.2.1) ≠ ⟨ij.2, hj⟩ := by
    intro he
    have hev := congrArg Fin.val he
    exact (ne_of_lt hij) hev
  have hne : i ≠ j := by
    cases right
    · exact hne0
    · exact Ne.symm hne0
  let a := ((ω k.val).1.2.2.2 i).1
  have hlabel : liveLabelAt (ω k.val).1 (if right then ij.2 else ij.1) = a := by
    cases right
    · change liveLabelAt (ω k.val).1 ij.1 = ((ω k.val).1.2.2.2 ⟨ij.1, hi⟩).1
      simp only [liveLabelAt, dite_eq_left hi]
    · change liveLabelAt (ω k.val).1 ij.2 = ((ω k.val).1.2.2.2 ⟨ij.2, hj⟩).1
      simp only [liveLabelAt, dite_eq_left hj]
  have hp := sample_clade_pair_proper N (ω k.val).1 (hvalid k.val)
    (fun v => ancestorLabel N ω leftBoundaryProbe v k.val)
    (kingman_path_sample_surjective N ω hinit hvalid hstep k.val) i j hne
  let c := historyClade N (fun j : Fin N => ω j.val) k.val a
  have hcn : c ≠ ∅ ∧ c ≠ Finset.univ := by
    dsimp only [c]
    rw [historyClade_of_path N ω k.val a (by omega)]
    exact ⟨hp.1.ne_empty, hp.2⟩
  have hmono : Monotone (fun k => (ω k).1.1) :=
    monotone_nat_of_le_succ (fun k => (hstep k).time_le)
  have hlo := pair_birth_time_le_current_time ω (hvalid 0).1 hmono k.val a
  have htime := kingman_path_time_strict_next N ω hinit hstep k.val hk
  have hlt : pairBirthTime ω k.val a < (ω (k.val + 1)).1.1 := lt_of_le_of_lt hlo htime
  change 0 < branchLength (historyChildBranch N (fun j : Fin N => ω j.val) k right) ∧ _
  rw [historyChildBranch_of_path_pair N ω k ij hev hij hj right, hlabel]
  have hc0 : ¬ (c = ∅ ∨ c = Finset.univ) := by
    intro h
    rcases h with h | h
    · exact hcn.1 h
    · exact hcn.2 h
  have hefinite : finiteBranch c (pairBirthTime ω k.val a) (ω (k.val + 1)).1.1 =
      (c, pairBirthTime ω k.val a, (ω (k.val + 1)).1.1) := by
    simp only [finiteBranch, hc0, ite_false, max_eq_right hlt.le]
  change 0 < branchLength (finiteBranch c (pairBirthTime ω k.val a)
      (ω (k.val + 1)).1.1) ∧
    (finiteBranch c (pairBirthTime ω k.val a) (ω (k.val + 1)).1.1).2.1 ≤ (ω k.val).1.1 ∧
    (finiteBranch c (pairBirthTime ω k.val a) (ω (k.val + 1)).1.1).2.2 = (ω (k.val + 1)).1.1
  rw [hefinite]
  simp only [branchLength, hc0, ite_false, max_eq_right (sub_nonneg.mpr hlt.le), sub_pos]
  exact ⟨hlt, hlo, trivial⟩

end Rhone.Coalescent.SmcPrime
