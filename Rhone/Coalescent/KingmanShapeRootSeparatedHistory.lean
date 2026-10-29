/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootPrefixPurity
public import Rhone.Coalescent.KingmanShapeRootPrefixCounts
public import Rhone.Combinatorics.KingmanShapeHistoryLength
public import Rhone.Combinatorics.KingmanHistoryTopology
/-!
# Root prefixes belong to the exact chronological interleaving fibre

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def rootSeparatedHistory (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) :
    SeparatedForestHistory (ADR11.singletonForest A.card)
      (ADR11.singletonForest (univ \ A).card) (A.card-1) ((univ \ A).card-1) := by
  have hG := (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h).1.2.2
  have hAr : A ∈ ADR11.roots
      ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
    rw [hs]
    exact mem_insert_self _ _
  have hBr : univ \ A ∈ ADR11.roots
      ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) := by
    rw [hs]
    exact mem_insert_of_mem (mem_singleton_self _)
  have hAc : 0 < A.card := (hG.1 A (mem_erase.mp (ADR11.roots_subset _ hAr)).2).card_pos
  have hBc : 0 < (univ \ A).card :=
    (hG.1 (univ \ A) (mem_erase.mp (ADR11.roots_subset _ hBr)).2).card_pos
  have hlen : A.card-1 + ((univ \ A).card-1) = n - 2 := by
    have hc := rootPartition_card A
    omega
  let hcast := Equiv.cast (congrArg (Combinatorics.RankedForestHistory (rootSumForest A)) hlen.symm)
    (rootPartitionPrefix n hn h A)
  refine ⟨hcast, ?_, ?_, ?_⟩
  · intro k hk
    rw [Combinatorics.historyAt_castLength _ _ _ hlen.symm]
    exact rootPartitionPrefix_pure n hn h A hs k (by omega)
  · rw [Combinatorics.historyEnd_castLength _ _ _ hlen.symm,
      (rootPartitionPrefix_root_counts n hn h A hs).1, ADR11.card_roots_singletonForest]
    omega
  · rw [Combinatorics.historyEnd_castLength _ _ _ hlen.symm,
      (rootPartitionPrefix_root_counts n hn h A hs).2, ADR11.card_roots_singletonForest]
    omega
end Rhone.Coalescent
