/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeHistoryTrace
public import Rhone.Coalescent.KingmanForestEmbedding
/-! # Subtree mergers remain mergers in disjoint sum-tagged forests -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem historyAt_isForest {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (h : Combinatorics.RankedForestHistory F t) (k : ℕ) : ADR11.IsForest
        (Combinatorics.historyAt F t h k) := by
  induction t generalizing F k with
  | zero => exact hF
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    cases k with
    | zero => exact hF
    | succ k => exact ih G.1 (hF.of_mem_merges G.2).1 h k
private theorem shape_sum_left_root {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M)) (hF : ADR11.IsForest F)
    (B : Finset L) (hB : B ∈ ADR11.roots F) :
    B.map (Function.Embedding.inl : L ↪ L ⊕ M) ∈ ADR11.roots
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H) := by
  apply ADR11.mem_roots.mpr
  refine ⟨mem_union_left _ (mem_image.mpr ⟨B, ADR11.roots_subset F hB, rfl⟩), ?_⟩
  intro D hD hBD
  rcases mem_union.mp hD with hD | hD
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    exact congrArg (fun X => X.map Function.Embedding.inl)
      ((ADR11.mem_roots.mp hB).2 C hC (map_subset_map.mp hBD))
  · obtain ⟨C, _, rfl⟩ := mem_image.mp hD
    obtain ⟨b, hb⟩ := hF.1 B (ADR11.roots_subset F hB)
    have hin := hBD (mem_map.mpr ⟨b, hb, rfl⟩)
    obtain ⟨c, _, he⟩ := mem_map.mp hin
    cases he
theorem history_sum_left_merge {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F G : Finset (Finset L)) (H : Finset (Finset M)) (hF : ADR11.IsForest F)
    (hG : G ∈ ADR11.merges F) :
    forestEmbed Function.Embedding.inl G ∪ forestEmbed Function.Embedding.inr H ∈
      ADR11.merges (forestEmbed Function.Embedding.inl F ∪
        forestEmbed Function.Embedding.inr H) := by
  obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hG
  apply ADR11.mem_merges.mpr
  refine ⟨B.map Function.Embedding.inl, shape_sum_left_root F H hF B hB,
    C.map Function.Embedding.inl, shape_sum_left_root F H hF C hC, ?_, ?_⟩
  · exact fun he => hBC ((map_injective Function.Embedding.inl) he)
  · rw [forestEmbed_insert, map_union, insert_union]
private theorem shape_sum_right_root {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M)) (hH : ADR11.IsForest H)
    (B : Finset M) (hB : B ∈ ADR11.roots H) :
    B.map (Function.Embedding.inr : M ↪ L ⊕ M) ∈ ADR11.roots
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H) := by
  apply ADR11.mem_roots.mpr
  refine ⟨mem_union_right _ (mem_image.mpr ⟨B, ADR11.roots_subset H hB, rfl⟩), ?_⟩
  intro D hD hBD
  rcases mem_union.mp hD with hD | hD
  · obtain ⟨C, _, rfl⟩ := mem_image.mp hD
    obtain ⟨b, hb⟩ := hH.1 B (ADR11.roots_subset H hB)
    have hin := hBD (mem_map.mpr ⟨b, hb, rfl⟩)
    obtain ⟨c, _, he⟩ := mem_map.mp hin
    cases he
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    exact congrArg (fun X => X.map Function.Embedding.inr)
      ((ADR11.mem_roots.mp hB).2 C hC (map_subset_map.mp hBD))
theorem history_sum_right_merge {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H G : Finset (Finset M)) (hH : ADR11.IsForest H)
    (hG : G ∈ ADR11.merges H) :
    forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr G ∈
      ADR11.merges (forestEmbed Function.Embedding.inl F ∪
        forestEmbed Function.Embedding.inr H) := by
  obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hG
  apply ADR11.mem_merges.mpr
  refine ⟨B.map Function.Embedding.inr, shape_sum_right_root F H hH B hB,
    C.map Function.Embedding.inr, shape_sum_right_root F H hH C hC, ?_, ?_⟩
  · exact fun he => hBC ((map_injective Function.Embedding.inr) he)
  · rw [forestEmbed_insert, map_union, union_insert]
end Rhone.Coalescent
