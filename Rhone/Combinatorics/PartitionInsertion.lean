/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Insertion and deletion in integer partitions -/

@[expose] public section
namespace Rhone.Combinatorics
open Finset

def partitionDeleteParts (s : Multiset ℕ) (j : ℕ) : Multiset ℕ :=
  if j = 1 then s.erase j else (j - 1) ::ₘ s.erase j

def partitionDelete {n : ℕ} (p : Nat.Partition (n + 1)) (j : ℕ)
    (hj : j ∈ p.parts) : Nat.Partition n where
  parts := partitionDeleteParts p.parts j
  parts_pos := by
    intro i hi
    unfold partitionDeleteParts at hi
    split_ifs at hi with h
    · exact p.parts_pos (Multiset.mem_of_mem_erase hi)
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · have := p.parts_pos hj
        omega
      · exact p.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    have hsum := Multiset.sum_erase hj
    have hp := p.parts_sum
    unfold partitionDeleteParts
    split_ifs with h
    · omega
    · simp only [Multiset.sum_cons]
      have := p.parts_pos hj
      omega

def partitionInsert {n : ℕ} (q : Nat.Partition n) (j : ℕ)
    (hj : j = 0 ∨ j ∈ q.parts) : Nat.Partition (n + 1) where
  parts := if j = 0 then 1 ::ₘ q.parts else (j + 1) ::ₘ q.parts.erase j
  parts_pos := by
    intro i hi
    split_ifs at hi with h
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · omega
      · exact q.parts_pos hi
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · omega
      · exact q.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    split_ifs with h
    · simp [q.parts_sum, Nat.add_comm]
    · have hmem : j ∈ q.parts := hj.resolve_left h
      have he := Multiset.sum_erase hmem
      simp only [Multiset.sum_cons]
      have hq := q.parts_sum
      omega

theorem partitionInsert_mem {n : ℕ} (q : Nat.Partition n) (j : ℕ)
    (hj : j = 0 ∨ j ∈ q.parts) : j + 1 ∈ (partitionInsert q j hj).parts := by
  unfold partitionInsert
  split_ifs with h
  · subst j
    exact Multiset.mem_cons_self _ _
  · exact Multiset.mem_cons_self _ _

theorem partitionDelete_insert {n : ℕ} (q : Nat.Partition n) (j : ℕ)
    (hj : j = 0 ∨ j ∈ q.parts) :
    partitionDelete (partitionInsert q j hj) (j + 1) (partitionInsert_mem q j hj) = q := by
  apply Nat.Partition.ext
  unfold partitionDelete partitionDeleteParts partitionInsert
  by_cases h : j = 0
  · subst j
    simp
  · have h1 : j + 1 ≠ 1 := by omega
    simp only [h, h1, ite_false, Nat.add_sub_cancel,
      Multiset.erase_cons_head]
    exact Multiset.cons_erase (hj.resolve_left h)

theorem partitionDelete_index {n : ℕ} (p : Nat.Partition (n + 1)) (j : ℕ)
    (hj : j ∈ p.parts) :
    j - 1 = 0 ∨ j - 1 ∈ (partitionDelete p j hj).parts := by
  by_cases h : j = 1
  · left
    omega
  · right
    simp [partitionDelete, partitionDeleteParts, h]

theorem partitionInsert_delete {n : ℕ} (p : Nat.Partition (n + 1)) (j : ℕ)
    (hj : j ∈ p.parts) :
    partitionInsert (partitionDelete p j hj) (j - 1) (partitionDelete_index p j hj) = p := by
  apply Nat.Partition.ext
  have hpos := p.parts_pos hj
  unfold partitionInsert partitionDelete partitionDeleteParts
  by_cases h : j = 1
  · subst j
    simpa using Multiset.cons_erase hj
  · have h0 : j - 1 ≠ 0 := by omega
    simp only [h0, h, ite_false, Multiset.erase_cons_head,
      Nat.sub_add_cancel hpos]
    exact Multiset.cons_erase hj

theorem sum_partition_individual_delete {M : Type*} [AddCommMonoid M]
    (n : ℕ) (g : Multiset ℕ → ℕ → M) :
    (∑ p : Nat.Partition (n + 1), ∑ j ∈ p.parts.toFinset, g p.parts j) =
      ∑ q : Nat.Partition n, (g (1 ::ₘ q.parts) 1 +
        ∑ j ∈ q.parts.toFinset, g ((j + 1) ::ₘ q.parts.erase j) (j + 1)) := by
  classical
  have hzero (q : Nat.Partition n) : 0 ∉ q.parts.toFinset := by
    intro h
    exact (q.parts_pos (Multiset.mem_toFinset.1 h)).false
  have hrhs : (∑ q : Nat.Partition n, (g (1 ::ₘ q.parts) 1 +
        ∑ j ∈ q.parts.toFinset, g ((j + 1) ::ₘ q.parts.erase j) (j + 1))) =
      ∑ q : Nat.Partition n, ∑ j ∈ insert 0 q.parts.toFinset,
        g (if j = 0 then 1 ::ₘ q.parts else (j + 1) ::ₘ q.parts.erase j) (j + 1) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_insert (hzero q)]
    simp only [ite_true, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hne : j ≠ 0 := (q.parts_pos (Multiset.mem_toFinset.1 hj)).ne'
    simp [hne]
  rw [hrhs, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun a ha =>
    ⟨partitionDelete a.1 a.2 (Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2), a.2 - 1⟩)
    (fun b hb => ⟨partitionInsert b.1 b.2 (by
      simpa only [Finset.mem_insert, Multiset.mem_toFinset] using (Finset.mem_sigma.1 hb).2),
      b.2 + 1⟩) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_insert,
      Multiset.mem_toFinset]
    exact partitionDelete_index _ _ _
  · intro b hb
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Multiset.mem_toFinset]
    exact partitionInsert_mem _ _ _
  · intro a ha
    have hpos := a.1.parts_pos (Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2)
    exact Sigma.ext (partitionInsert_delete a.1 a.2
      (Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2)) (heq_of_eq (by
        change a.2 - 1 + 1 = a.2
        omega))
  · intro b hb
    exact Sigma.ext (partitionDelete_insert b.1 b.2 (by
      simpa only [Finset.mem_insert, Multiset.mem_toFinset] using
        (Finset.mem_sigma.1 hb).2)) (heq_of_eq (by change b.2 + 1 - 1 = b.2; omega))
  · intro a ha
    have hpos := a.1.parts_pos (Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2)
    have hj := Multiset.mem_toFinset.1 (Finset.mem_sigma.1 ha).2
    change g a.1.parts a.2 =
      g (partitionInsert (partitionDelete a.1 a.2 hj) (a.2 - 1)
        (partitionDelete_index a.1 a.2 hj)).parts (a.2 - 1 + 1)
    rw [partitionInsert_delete, Nat.sub_add_cancel hpos]

end Rhone.Combinatorics
