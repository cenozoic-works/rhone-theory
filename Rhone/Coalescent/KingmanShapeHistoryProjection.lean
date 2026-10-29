/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistoryInterleave
public import Rhone.Coalescent.KingmanForestPreimage
/-! # Recover subtree forests and their chronological merger counters -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem historyAt_root_count {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (h : Combinatorics.RankedForestHistory F t) (k : ℕ) (hk : k ≤ t) :
    (ADR11.roots (Combinatorics.historyAt F t h k)).card + k = (ADR11.roots F).card := by
  induction t generalizing F k with
  | zero =>
    have he : k = 0 := by omega
    subst k
    rfl
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    cases k with
    | zero => simp only [Combinatorics.historyAt, Nat.add_zero]
    | succ k =>
      obtain ⟨hG, hc, _⟩ := hF.of_mem_merges G.2
      have he := ih G.1 hG h k (by omega)
      change (ADR11.roots (Combinatorics.historyAt G.1 t h k)).card + (k + 1) = _
      omega
theorem history_sum_left_projection {L M : Type*} [Fintype L]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M)) (hH : ADR11.IsForest H) :
    forestPreimage (Function.Embedding.inl : L ↪ L ⊕ M)
      ((forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H).filter
        (fun C => C ⊆ (univ : Finset L).map Function.Embedding.inl)) = F := by
  have he : (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H).filter
      (fun C => C ⊆ (univ : Finset L).map Function.Embedding.inl) =
      forestEmbed (Function.Embedding.inl : L ↪ L ⊕ M) F := by
    ext C
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hC, hCL⟩
      rcases hC with hC | hC
      · exact hC
      · obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
        obtain ⟨d, hd⟩ := hH.1 D hD
        have hm := hCL (mem_map.mpr ⟨d, hd, rfl⟩)
        obtain ⟨x, _, hx⟩ := mem_map.mp hm
        cases hx
    · intro hC
      refine ⟨Or.inl hC, ?_⟩
      obtain ⟨D, _, rfl⟩ := mem_image.mp hC
      exact map_subset_map.mpr (subset_univ _)
  rw [he, forestPreimage_forestEmbed]
theorem history_sum_right_projection {L M : Type*} [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M)) (hF : ADR11.IsForest F) :
    forestPreimage (Function.Embedding.inr : M ↪ L ⊕ M)
      ((forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H).filter
        (fun C => C ⊆ (univ : Finset M).map Function.Embedding.inr)) = H := by
  have he : (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H).filter
      (fun C => C ⊆ (univ : Finset M).map Function.Embedding.inr) =
      forestEmbed (Function.Embedding.inr : M ↪ L ⊕ M) H := by
    ext C
    simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨hC, hCR⟩
      rcases hC with hC | hC
      · obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
        obtain ⟨d, hd⟩ := hF.1 D hD
        have hm := hCR (mem_map.mpr ⟨d, hd, rfl⟩)
        obtain ⟨x, _, hx⟩ := mem_map.mp hm
        cases hx
      · exact hC
    · intro hC
      refine ⟨Or.inr hC, ?_⟩
      obtain ⟨D, _, rfl⟩ := mem_image.mp hC
      exact map_subset_map.mpr (subset_univ _)
  rw [he, forestPreimage_forestEmbed]
end Rhone.Coalescent
