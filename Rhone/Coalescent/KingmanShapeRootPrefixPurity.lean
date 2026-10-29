/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootPrefix
public import Rhone.Coalescent.KingmanShapeRootPartitionRange
public import Rhone.Coalescent.KingmanShapeRootPurity
public import Rhone.Coalescent.KingmanShapeSeparatedHistory
/-!
# Tagged root-prefix forests stay inside the two daughter ranges

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem rootPartitionPrefix_pure (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) (k : ℕ) (hk : k ≤ n - 2) :
    SumPureForest (Combinatorics.historyAt (rootSumForest A) (n - 2) (rootPartitionPrefix n hn h A)
        k) := by
  intro C hC
  have hmap := historyAt_rootPartitionPrefix n hn h A k hk
  have hCE : C.map (rootPartitionEquiv A).toEmbedding ∈
      Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k := by
    rw [← hmap]
    exact mem_image.mpr ⟨C, hC, rfl⟩
  rcases historyAt_root_split_pure n hn h A hs k hk _ hCE with hleft | hright
  · apply Or.inl
    have hmapped : C.map (rootPartitionEquiv A).toEmbedding ⊆
        ((univ : Finset (Fin A.card)).map Function.Embedding.inl).map
          (rootPartitionEquiv A).toEmbedding := by
      calc
        _ ⊆ A := hleft
        _ = _ := (rootPartitionRange_left A).symm
    exact map_subset_map.mp hmapped
  · apply Or.inr
    have hmapped : C.map (rootPartitionEquiv A).toEmbedding ⊆
        ((univ : Finset (Fin (univ \ A).card)).map Function.Embedding.inr).map
          (rootPartitionEquiv A).toEmbedding := by
      calc
        _ ⊆ univ \ A := hright
        _ = _ := (rootPartitionRange_right A).symm
    exact map_subset_map.mp hmapped
end Rhone.Coalescent
