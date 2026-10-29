/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootPrefix
public import Rhone.Coalescent.KingmanShapeRootPartitionRange
public import Rhone.Coalescent.KingmanShapeFullRoot
/-!
# Root-prefix daughter projections end with exactly one root each

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem rootPartitionPrefix_left_full (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) :
    (univ : Finset (Fin A.card)).map Function.Embedding.inl ∈
      Combinatorics.historyEnd (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A) := by
  have hm : A ∈ (Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ := by
    apply ADR11.roots_subset
    rw [hs]
    exact mem_insert_self _ _
  have hmapped : ((univ : Finset (Fin A.card)).map Function.Embedding.inl).map
      (rootPartitionEquiv A).toEmbedding ∈ forestEmbed (rootPartitionEquiv A).toEmbedding
        (Combinatorics.historyEnd (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A)) := by
    rw [historyEnd_rootPartitionPrefix n hn h A, rootPartitionRange_left A]
    exact hm
  obtain ⟨D, hD, he⟩ := mem_image.mp hmapped
  exact (map_injective (rootPartitionEquiv A).toEmbedding he) ▸ hD
theorem rootPartitionPrefix_right_full (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) :
    (univ : Finset (Fin (univ \ A).card)).map Function.Embedding.inr ∈
      Combinatorics.historyEnd (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A) := by
  have hm : univ \ A ∈ (Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ :=
      by
    apply ADR11.roots_subset
    rw [hs]
    exact mem_insert_of_mem (mem_singleton_self _)
  have hmapped : ((univ : Finset (Fin (univ \ A).card)).map Function.Embedding.inr).map
      (rootPartitionEquiv A).toEmbedding ∈ forestEmbed (rootPartitionEquiv A).toEmbedding
        (Combinatorics.historyEnd (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A)) := by
    rw [historyEnd_rootPartitionPrefix n hn h A, rootPartitionRange_right A]
    exact hm
  obtain ⟨D, hD, he⟩ := mem_image.mp hmapped
  exact (map_injective (rootPartitionEquiv A).toEmbedding he) ▸ hD
theorem rootPartitionPrefix_root_counts (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) :
    (ADR11.roots (sumLeftForest
      (Combinatorics.historyEnd (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A)))).card =
          1 ∧
    (ADR11.roots (sumRightForest
      (Combinatorics.historyEnd (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A)))).card =
          1 :=
  ⟨sumLeftForest_full_root _ (rootPartitionPrefix_left_full n hn h A hs),
    sumRightForest_full_root _ (rootPartitionPrefix_right_full n hn h A hs)⟩
end Rhone.Coalescent
