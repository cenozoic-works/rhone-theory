/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootLabels
public import Rhone.Coalescent.KingmanShapeForestEmbedLaws
/-!
# The tagged daughter label partition covers exactly the daughter clades

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem rootPartitionRange_left {n : ℕ} (A : Finset (Fin n)) :
    ((univ : Finset (Fin A.card)).map Function.Embedding.inl).map
      (rootPartitionEquiv A).toEmbedding = A := by
  rw [map_map]
  have he : (Function.Embedding.inl : Fin A.card ↪ Fin A.card ⊕ Fin (univ \ A).card).trans
      (rootPartitionEquiv A).toEmbedding = cladeLabelEmbedding A :=
    Function.Embedding.ext (fun x => rootPartitionEquiv_inl A x)
  rw [he, cladeLabelEmbedding_range]
theorem rootPartitionRange_right {n : ℕ} (A : Finset (Fin n)) :
    ((univ : Finset (Fin (univ \ A).card)).map Function.Embedding.inr).map
      (rootPartitionEquiv A).toEmbedding = univ \ A := by
  rw [map_map]
  have he : (Function.Embedding.inr : Fin (univ \ A).card ↪
      Fin A.card ⊕ Fin (univ \ A).card).trans
      (rootPartitionEquiv A).toEmbedding = cladeLabelEmbedding (univ \ A) :=
    Function.Embedding.ext (fun x => rootPartitionEquiv_inr A x)
  rw [he, cladeLabelEmbedding_range]
theorem rootPartition_card {n : ℕ} (A : Finset (Fin n)) : A.card + (univ \ A).card = n := by
  rw [card_sdiff_of_subset (subset_univ A), card_univ, Fintype.card_fin]
  have hc := card_le_card (subset_univ A)
  rw [card_univ, Fintype.card_fin] at hc
  omega
end Rhone.Coalescent
