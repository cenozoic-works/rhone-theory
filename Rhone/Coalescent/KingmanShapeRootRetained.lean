/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootDecomposition
public import Rhone.Coalescent.KingmanShapeCladeFilterRelabel
/-!
# Recovered daughter chronology equals the retained daughter forests

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
private theorem forestPreimage_embed_comp {L M N : Type*}
    [DecidableEq L] [DecidableEq M] [DecidableEq N]
    (e : L ↪ M) (f : M ↪ N) (W : Finset (Finset M)) :
    forestPreimage (e.trans f) (forestEmbed f W) = forestPreimage e W := by
  simp only [forestPreimage, forestEmbed, image_image]
  apply image_congr
  intro C hC
  ext x
  dsimp only [Function.comp_apply]
  simp only [mem_preimage]
  change f (e x) ∈ C.map f ↔ e x ∈ C
  exact mem_map' f
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryDecomposition_left_retained (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) (k : ℕ) (hk : k ≤ n - 2) :
    let p := rootHistoryDecomposition n hn h A hs
    forestPreimage (cladeLabelEmbedding A)
      ((Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k).filter (fun C => C ⊆ A)) =
      Combinatorics.historyAt _ (A.card - 1) p.1.1 (Combinatorics.interleavingLeft p.2 k) := by
  dsimp only
  let p := rootHistoryDecomposition n hn h A hs
  let W := forestEmbed Function.Embedding.inl
      (Combinatorics.historyAt _ (A.card - 1) p.1.1 (Combinatorics.interleavingLeft p.2 k)) ∪
    forestEmbed Function.Embedding.inr
      (Combinatorics.historyAt _ ((univ \ A).card - 1) p.1.2
          (Combinatorics.interleavingRight p.2 k))
  have he := historyAt_rootHistoryDecomposition n hn h A hs k hk
  have hemb : (Function.Embedding.inl : Fin A.card ↪
      Fin A.card ⊕ Fin (univ \ A).card).trans (rootPartitionEquiv A).toEmbedding =
      cladeLabelEmbedding A := Function.Embedding.ext (fun x => rootPartitionEquiv_inl A x)
  rw [← he, ← forestEmbed_filter_clade (rootPartitionEquiv A).toEmbedding
    ((univ : Finset (Fin A.card)).map Function.Embedding.inl) A (rootPartitionRange_left A),
    ← hemb, forestPreimage_embed_comp]
  exact history_sum_left_projection _ _
    (historyAt_isForest _ (ADR11.isForest_singletonForest _) _ p.1.2 _)
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryDecomposition_right_retained (n : ℕ) (hn : 2 ≤ n)
    (h : Combinatorics.RankedLabelledHistory n) (A : Finset (Fin n))
    (hs : ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A}) (k : ℕ) (hk : k ≤ n - 2) :
    let p := rootHistoryDecomposition n hn h A hs
    forestPreimage (cladeLabelEmbedding (univ \ A))
      ((Combinatorics.historyAt (ADR11.singletonForest n) (n - 1) h k).filter
          (fun C => C ⊆ univ \ A)) =
      Combinatorics.historyAt _ ((univ \ A).card - 1) p.1.2
          (Combinatorics.interleavingRight p.2 k) := by
  dsimp only
  let p := rootHistoryDecomposition n hn h A hs
  let W := forestEmbed Function.Embedding.inl
      (Combinatorics.historyAt _ (A.card - 1) p.1.1 (Combinatorics.interleavingLeft p.2 k)) ∪
    forestEmbed Function.Embedding.inr
      (Combinatorics.historyAt _ ((univ \ A).card - 1) p.1.2
          (Combinatorics.interleavingRight p.2 k))
  have he := historyAt_rootHistoryDecomposition n hn h A hs k hk
  have hemb : (Function.Embedding.inr : Fin (univ \ A).card ↪
      Fin A.card ⊕ Fin (univ \ A).card).trans (rootPartitionEquiv A).toEmbedding =
      cladeLabelEmbedding (univ \ A) := Function.Embedding.ext (fun x => rootPartitionEquiv_inr A x)
  rw [← he, ← forestEmbed_filter_clade (rootPartitionEquiv A).toEmbedding
    ((univ : Finset (Fin (univ \ A).card)).map Function.Embedding.inr)
    (univ \ A) (rootPartitionRange_right A),
    ← hemb, forestPreimage_embed_comp]
  exact history_sum_right_projection _ _
    (historyAt_isForest _ (ADR11.isForest_singletonForest _) _ p.1.1 _)
end Rhone.Coalescent
