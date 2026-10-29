/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeCladePreimageRelabel
/-!
# Retained daughter forests commute with global leaf relabelling

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem forestEmbed_filter_clade {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (A : Finset L) (B : Finset M) (hAB : A.map e = B)
    (W : Finset (Finset L)) :
    forestEmbed e (W.filter (fun C => C ⊆ A)) =
      (forestEmbed e W).filter (fun C => C ⊆ B) := by
  ext D
  constructor
  · intro hD
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    obtain ⟨hCW, hCA⟩ := mem_filter.mp hC
    apply mem_filter.mpr
    refine ⟨mem_image.mpr ⟨C, hCW, rfl⟩, ?_⟩
    rw [← hAB]
    exact map_subset_map.mpr hCA
  · intro hD
    obtain ⟨hDW, hDB⟩ := mem_filter.mp hD
    obtain ⟨C, hCW, rfl⟩ := mem_image.mp hDW
    rw [← hAB] at hDB
    exact mem_image.mpr ⟨C, mem_filter.mpr ⟨hCW, map_subset_map.mp hDB⟩, rfl⟩
theorem retainedSubtree_relabel (n : ℕ) (e : Equiv.Perm (Fin n))
    (A B : Finset (Fin n)) (hAB : A.map e.toEmbedding = B)
    (W : Finset (Finset (Fin n))) :
    forestPreimage (cladeLabelEmbedding B)
        ((forestEmbed e.toEmbedding W).filter (fun C => C ⊆ B)) =
      forestEmbed (cladeRelabelEquiv n e A B hAB).toEmbedding
        (forestPreimage (cladeLabelEmbedding A) (W.filter (fun C => C ⊆ A))) := by
  rw [← forestEmbed_filter_clade e.toEmbedding A B hAB W, forestPreimage_relabel_clade]
end Rhone.Coalescent
