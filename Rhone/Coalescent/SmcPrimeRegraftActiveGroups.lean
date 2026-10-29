/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeBranchActive
/-!
# Distinct active clades within the three groups of old branches in the regraft

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

def ActiveCladeDistinct {N : ℕ} (q : ℝ) (b c : Branch N) : Prop :=
  BranchActive b q → BranchActive c q → b.1 ≠ c.1

theorem below_cut_pairwise {N : ℕ} (T : Tree N) (hnorm : TreeNormalized T)
    (hunique : TreeActiveUnique T) (t q : ℝ) (hq : 0 ≤ q) :
    (((List.finRange T.1).map (fun i => belowCut (T.2 i) t))).Pairwise
      (ActiveCladeDistinct q) := by
  rw [List.pairwise_map]
  apply (List.nodup_finRange T.1).pairwise_of_forall_ne
  intro i _ j _ hij hia hja heq
  have hi := (below_cut_active T hnorm t q i hia).1
  have hj := (below_cut_active T hnorm t q j hja).1
  apply hij
  apply hunique q hq i (by simpa [activeBranches, BranchActive] using hi)
    j (by simpa [activeBranches, BranchActive] using hj)
  exact heq

theorem between_cut_pairwise {N : ℕ} (T : Tree N) (hnorm : TreeNormalized T)
    (hchron : TreeChronology T) (hunique : TreeActiveUnique T)
    (s : Finset (Fin N)) (t a q : ℝ) (hq : 0 ≤ q) :
    (((List.finRange T.1).map (fun i => betweenCutAttachment (T.2 i) s t a))).Pairwise
      (ActiveCladeDistinct q) := by
  classical
  rw [List.pairwise_map]
  apply (List.nodup_finRange T.1).pairwise_of_forall_ne
  intro i _ j _ hij hia hja heq
  have hi := between_cut_active T hnorm s t a q i hia
  have hj := between_cut_active T hnorm s t a q j hja
  change (T.2 i).1 \ s = (T.2 j).1 \ s at heq
  have hcl : (T.2 i).1 = (T.2 j).1 := by
    by_contra hn
    have hd := (hchron.1 q hq).2.2 _ (branch_active_time_clade T q i hi.1)
      _ (branch_active_time_clade T q j hj.1) hn
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hi.2.2.2
    have hxj : x ∈ (T.2 j).1 \ s := by rwa [← heq]
    exact Finset.disjoint_left.mp hd (Finset.mem_sdiff.mp hx).1
      (Finset.mem_sdiff.mp hxj).1
  exact hij (hunique q hq i (by simpa [activeBranches, BranchActive] using hi.1)
    j (by simpa [activeBranches, BranchActive] using hj.1) hcl)

theorem above_attachment_pairwise {N : ℕ} (T : Tree N) (hnorm : TreeNormalized T)
    (hchron : TreeChronology T) (hunique : TreeActiveUnique T)
    (s target : Finset (Fin N)) (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hat : target ∈ timeClades T a) :
    (((List.finRange T.1).map (fun i => aboveAttachment (T.2 i) s target a))).Pairwise
      (ActiveCladeDistinct q) := by
  classical
  rw [List.pairwise_map]
  apply (List.nodup_finRange T.1).pairwise_of_forall_ne
  intro i _ j _ hij hia hja heq
  have hi := above_attachment_active T hnorm s target a q i hia
  have hj := above_attachment_active T hnorm s target a q j hja
  change regraftClade s target (T.2 i).1 = regraftClade s target (T.2 j).1 at heq
  have hcl : (T.2 i).1 = (T.2 j).1 := by
    by_contra hn
    have hd := chronology_regraft_clades_disjoint T hchron s target a q ha hi.2.1
      hat _ _ (branch_active_time_clade T q i hi.1)
      (branch_active_time_clade T q j hj.1) hn
    rw [heq] at hd
    exact hj.2.2 ((Finset.disjoint_self_iff_empty _).mp hd)
  exact hij (hunique q hq i (by simpa [activeBranches, BranchActive] using hi.1)
    j (by simpa [activeBranches, BranchActive] using hj.1) hcl)

theorem treeOfList_active_unique_of_pairwise {N : ℕ} (l : List (Branch N))
    (hpair : ∀ q, 0 ≤ q → l.Pairwise (ActiveCladeDistinct q)) :
    TreeActiveUnique (treeOfList l) := by
  intro q hq i hi j hj he
  simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · exact (hpair q hq).rel_get_of_lt hij hi hj he
  · exact (hpair q hq).rel_get_of_lt hji hj hi he.symm
end Rhone.Coalescent.SmcPrime
