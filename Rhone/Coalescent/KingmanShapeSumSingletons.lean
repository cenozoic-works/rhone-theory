/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootLabels
public import Rhone.Coalescent.KingmanShapeForestEmbedLaws
/-!
# Singleton starting forests under tagged daughter label bijections

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem sumSingletonForest_mem (a b : ℕ) (x : Fin a ⊕ Fin b) :
    {x} ∈ forestEmbed Function.Embedding.inl (ADR11.singletonForest a) ∪
      forestEmbed Function.Embedding.inr (ADR11.singletonForest b) := by
  cases x with
  | inl x =>
    apply mem_union_left
    exact mem_image.mpr ⟨{x}, mem_image.mpr ⟨x, mem_univ _, rfl⟩,
      (map_singleton Function.Embedding.inl x).symm⟩
  | inr x =>
    apply mem_union_right
    exact mem_image.mpr ⟨{x}, mem_image.mpr ⟨x, mem_univ _, rfl⟩,
      (map_singleton Function.Embedding.inr x).symm⟩
theorem sumSingletonForest_member (a b : ℕ) (D : Finset (Fin a ⊕ Fin b))
    (hD : D ∈ forestEmbed Function.Embedding.inl (ADR11.singletonForest a) ∪
      forestEmbed Function.Embedding.inr (ADR11.singletonForest b)) :
    ∃ x : Fin a ⊕ Fin b, D = {x} := by
  rcases mem_union.mp hD with hL | hR
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp hL
    obtain ⟨x, _, rfl⟩ := mem_image.mp hC
    exact ⟨Sum.inl x, map_singleton _ _⟩
  · obtain ⟨C, hC, rfl⟩ := mem_image.mp hR
    obtain ⟨x, _, rfl⟩ := mem_image.mp hC
    exact ⟨Sum.inr x, map_singleton _ _⟩
theorem singletonForest_sum_embed (a b n : ℕ) (e : Fin a ⊕ Fin b ≃ Fin n) :
    forestEmbed e.toEmbedding
        (forestEmbed Function.Embedding.inl (ADR11.singletonForest a) ∪
          forestEmbed Function.Embedding.inr (ADR11.singletonForest b)) =
      ADR11.singletonForest n := by
  ext C
  constructor
  · intro hC
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
    obtain ⟨x, rfl⟩ := sumSingletonForest_member a b D hD
    exact mem_image.mpr ⟨e x, mem_univ _, (map_singleton e.toEmbedding x).symm⟩
  · intro hC
    obtain ⟨x, _, rfl⟩ := mem_image.mp hC
    exact mem_image.mpr ⟨{e.symm x}, sumSingletonForest_mem a b (e.symm x), by
      rw [map_singleton]
      change {e (e.symm x)} = {x}
      rw [Equiv.apply_symm_apply]⟩
end Rhone.Coalescent
