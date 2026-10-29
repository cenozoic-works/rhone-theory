/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanPartition
/-! # Finite label fibres under one fresh merger -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open Finset

theorem image_label_fibres_merge {L : Type*} [Fintype L] [DecidableEq L]
    (a : L → ℕ) (x y z : ℕ) (hx : ∃ i, a i = x) (hz : ∀ i, a i ≠ z) :
    (univ.image (fun i => univ.filter (fun j =>
      (if a j = x ∨ a j = y then z else a j) =
        (if a i = x ∨ a i = y then z else a i)))) =
    insert ((univ.filter (fun i => a i = x)) ∪ (univ.filter (fun i => a i = y)))
      ((univ.image (fun i => univ.filter (fun j => a j = a i))) \
        {univ.filter (fun i => a i = x), univ.filter (fun i => a i = y)}) := by
  classical
  let A : Finset L := univ.filter (fun i => a i = x)
  let B : Finset L := univ.filter (fun i => a i = y)
  let cell (i : L) : Finset L := univ.filter (fun j => a j = a i)
  let newCell (i : L) : Finset L := univ.filter (fun j =>
    (if a j = x ∨ a j = y then z else a j) =
      (if a i = x ∨ a i = y then z else a i))
  have hA (i : L) : cell i = A ↔ a i = x := by
    constructor
    · intro h
      have hm : i ∈ cell i := by simp [cell]
      rw [h] at hm
      exact (mem_filter.mp hm).2
    · intro h
      simp only [cell, A, h]
  have hB (i : L) : cell i = B ↔ a i = y := by
    constructor
    · intro h
      have hm : i ∈ cell i := by simp [cell]
      rw [h] at hm
      exact (mem_filter.mp hm).2
    · intro h
      simp only [cell, B, h]
  have hnew (i : L) : newCell i = if a i = x ∨ a i = y then A ∪ B else cell i := by
    by_cases hi : a i = x ∨ a i = y
    · rw [ite_eq_left hi]
      ext j
      by_cases hj : a j = x ∨ a j = y
      · rcases hj with hj | hj <;> simp [newCell, A, B, hi, hj]
      · simp only [newCell, A, B, mem_filter, mem_univ, true_and, mem_union,
          ite_eq_left hi, ite_eq_right hj]
        exact iff_of_false (hz j) hj
    · rw [ite_eq_right hi]
      ext j
      by_cases hj : a j = x ∨ a j = y
      · have hn : a j ≠ a i := by
          intro he
          exact hi (he ▸ hj)
        simp [newCell, cell, hi, hj, Ne.symm (hz i), hn]
      · simp [newCell, cell, hi, hj]
  change univ.image newCell = insert (A ∪ B) ((univ.image cell) \ {A, B})
  ext C
  constructor
  · rintro h
    obtain ⟨i, -, rfl⟩ := mem_image.mp h
    rw [hnew]
    by_cases hi : a i = x ∨ a i = y
    · simp [hi]
    · rw [ite_eq_right hi]
      apply mem_insert_of_mem
      refine mem_sdiff.mpr ⟨mem_image.mpr ⟨i, mem_univ i, rfl⟩, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hi (Or.inl ((hA i).mp h)), fun h => hi (Or.inr ((hB i).mp h))⟩
  · intro h
    rcases mem_insert.mp h with he | hc
    · subst C
      obtain ⟨i, hi⟩ := hx
      exact mem_image.mpr ⟨i, mem_univ i, by rw [hnew, ite_eq_left (Or.inl hi)]⟩
    · obtain ⟨hmem, hnot⟩ := mem_sdiff.mp hc
      obtain ⟨i, -, rfl⟩ := mem_image.mp hmem
      have hi : ¬ (a i = x ∨ a i = y) := by
        rintro (h | h)
        · exact hnot (mem_insert.mpr (Or.inl ((hA i).mpr h)))
        · exact hnot (mem_insert.mpr (Or.inr (mem_singleton.mpr ((hB i).mpr h))))
      exact mem_image.mpr ⟨i, mem_univ i, by rw [hnew, ite_eq_right hi]⟩
end Rhone.Coalescent.SmcPrime
