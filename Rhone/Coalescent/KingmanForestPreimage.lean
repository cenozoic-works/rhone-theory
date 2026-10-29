/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanForestEmbedding
/-! # Pulling back clades along an injective leaf-label map -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
universe u v
noncomputable def forestPreimage {L : Type u} {M : Type v} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (G : Finset (Finset M)) : Finset (Finset L) :=
  G.image (fun C => C.preimage e e.injective.injOn)
theorem forestPreimage_forestEmbed {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (F : Finset (Finset L)) : forestPreimage e (forestEmbed e F) = F := by
  unfold forestPreimage forestEmbed
  rw [image_image]
  have he : ((fun C => C.preimage e e.injective.injOn) ∘ (fun C => C.map e)) =
      (id : Finset L → Finset L) := by
    funext C
    exact preimage_map e C
  rw [he, image_id]
theorem forestEmbed_forestPreimage {L M : Type*} [Fintype L]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (G : Finset (Finset M))
    (hG : ∀ C ∈ G, C ⊆ (univ : Finset L).map e) :
    forestEmbed e (forestPreimage e G) = G := by
  have hc : ∀ C ∈ G, (C.preimage e e.injective.injOn).map e = C := by
    intro C hC
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      exact mem_preimage.mp hy
    · intro hx
      obtain ⟨y, _, rfl⟩ := mem_map.mp (hG C hC hx)
      exact mem_map.mpr ⟨y, mem_preimage.mpr hx, rfl⟩
  unfold forestEmbed forestPreimage
  rw [image_image]
  calc
    _ = G.image id := by
      apply image_congr
      intro C hC
      exact hc C hC
    _ = G := image_id
theorem isForest_forestEmbed_iff {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (F : Finset (Finset L)) :
    ADR11.IsForest (forestEmbed e F) ↔ ADR11.IsForest F := by
  constructor
  · intro hF
    constructor
    · intro C hC
      exact map_nonempty.mp (hF.1 (C.map e) (mem_image.mpr ⟨C, hC, rfl⟩))
    · intro C hC D hD
      rcases hF.2 (C.map e) (mem_image.mpr ⟨C, hC, rfl⟩)
          (D.map e) (mem_image.mpr ⟨D, hD, rfl⟩) with hCD | hDC | hd
      · exact Or.inl (map_subset_map.mp hCD)
      · exact Or.inr (Or.inl (map_subset_map.mp hDC))
      · exact Or.inr (Or.inr ((disjoint_map e).mp hd))
  · intro hF
    constructor
    · intro C hC
      obtain ⟨B, hB, rfl⟩ := mem_image.mp hC
      exact map_nonempty.mpr (hF.1 B hB)
    · intro C hC D hD
      obtain ⟨B, hB, rfl⟩ := mem_image.mp hC
      obtain ⟨E, hE, rfl⟩ := mem_image.mp hD
      rcases hF.2 B hB E hE with hBE | hEB | hd
      · exact Or.inl (map_subset_map.mpr hBE)
      · exact Or.inr (Or.inl (map_subset_map.mpr hEB))
      · exact Or.inr (Or.inr ((disjoint_map e).mpr hd))
end Rhone.Coalescent
