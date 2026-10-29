/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootDescent
/-!
# Chronological allocations are determined by their exact merger counters

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
private theorem interleaving_image_subset_of_left_counts {a b c d : ℕ}
    (s : Combinatorics.HistoryInterleaving a b) (t : Combinatorics.HistoryInterleaving c d)
    (hlen : a + b = c + d)
    (hc : ∀ k ≤ a + b, Combinatorics.interleavingLeft s k = Combinatorics.interleavingLeft t k) :
    s.1.image Fin.val ⊆ t.1.image Fin.val := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
  let z : Fin (c + d) := ⟨i.val, by omega⟩
  apply mem_image.mpr
  refine ⟨z, ?_, rfl⟩
  by_contra hz
  have hs := Combinatorics.interleaving_counts_succ s i
  have ht := Combinatorics.interleaving_counts_succ t z
  rw [ite_eq_left hi] at hs
  rw [ite_eq_right hz] at ht
  have hnow := hc i.val i.isLt.le
  have hnext := hc (i.val + 1) i.isLt
  dsimp only [z] at ht
  omega
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem interleaving_image_eq_of_left_counts {a b c d : ℕ}
    (s : Combinatorics.HistoryInterleaving a b) (t : Combinatorics.HistoryInterleaving c d)
    (hlen : a + b = c + d)
    (hc : ∀ k ≤ a + b, Combinatorics.interleavingLeft s k = Combinatorics.interleavingLeft t k) :
    s.1.image Fin.val = t.1.image Fin.val := by
  apply Subset.antisymm
  · exact interleaving_image_subset_of_left_counts s t hlen hc
  · apply interleaving_image_subset_of_left_counts t s hlen.symm
    intro k hk
    exact (hc k (by omega)).symm
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryDecomposition_slots_map (n : ℕ) (hn : 2 ≤ n)
    (h h' : Combinatorics.RankedLabelledHistory n) (A B : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A})
    (hs' : ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h').erase univ) =
      {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (hAB : A.map e.toEmbedding = B)
    (he : ∀ k ≤ n - 1, Combinatorics.forestRelabel e
        (Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k) =
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h' k) :
    (rootHistoryDecomposition n hn h A hs).2.1.image Fin.val =
      (rootHistoryDecomposition n hn h' B hs').2.1.image Fin.val := by
  have hlen (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
      (hs : ADR11.roots
          ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
        {A, univ \ A}) : A.card - 1 + ((univ \ A).card - 1) = n - 2 := by
    have hG := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h).1.2.2
    have hAr : A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
      rw [hs]; exact mem_insert_self _ _
    have hBr : univ \ A ∈ ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
      rw [hs]; exact mem_insert_of_mem (mem_singleton_self _)
    have hAc := (hG.1 A (mem_erase.mp (ADR11.roots_subset _ hAr)).2).card_pos
    have hBc := (hG.1 (univ \ A) (mem_erase.mp (ADR11.roots_subset _ hBr)).2).card_pos
    have hc := rootPartition_card A
    omega
  apply interleaving_image_eq_of_left_counts _ _ ((hlen h A hs).trans (hlen h' B hs').symm)
  intro k hk
  apply rootHistoryDecomposition_left_counter_map n hn h h' A B hs hs' e hAB he k
  rw [hlen h A hs] at hk
  exact hk
end Rhone.Coalescent
