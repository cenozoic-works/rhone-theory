/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanHistories
/-!
# Injective changes of leaf labels preserve Kingman forests and mergers

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
universe u v
def forestEmbed {L : Type u} {M : Type v} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (F : Finset (Finset L)) : Finset (Finset M) :=
  F.image (fun C => C.map e)
theorem forestEmbed_injective {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) : Function.Injective (forestEmbed e) :=
  image_injective (map_injective e)
theorem forestEmbed_insert {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (F : Finset (Finset L)) (C : Finset L) :
    forestEmbed e (insert C F) = insert (C.map e) (forestEmbed e F) := by
  simp only [forestEmbed, image_insert]
theorem roots_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F : Finset (Finset L)) :
    ADR11.roots (forestEmbed e F) = forestEmbed e (ADR11.roots F) := by
  ext D
  constructor
  · intro hD
    obtain ⟨hDF, hmax⟩ := ADR11.mem_roots.mp hD
    obtain ⟨C, hCF, rfl⟩ := mem_image.mp hDF
    apply mem_image.mpr
    refine ⟨C, ADR11.mem_roots.mpr ⟨hCF, ?_⟩, rfl⟩
    intro B hB hCB
    apply map_injective e
    exact hmax (B.map e) (mem_image.mpr ⟨B, hB, rfl⟩) (map_subset_map.mpr hCB)
  · intro hD
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    obtain ⟨hCF, hmax⟩ := ADR11.mem_roots.mp hC
    apply ADR11.mem_roots.mpr
    refine ⟨mem_image.mpr ⟨C, hCF, rfl⟩, ?_⟩
    intro D hD hCD
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
    exact congrArg (fun C => C.map e) (hmax B hB (map_subset_map.mp hCD))
theorem merges_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F : Finset (Finset L)) :
    ADR11.merges (forestEmbed e F) = (ADR11.merges F).image (forestEmbed e) := by
  ext G
  constructor
  · intro hG
    obtain ⟨B, hB, C, hC, hBC, he⟩ := ADR11.mem_merges.mp hG
    rw [roots_forestEmbed] at hB hC
    obtain ⟨B', hB', rfl⟩ := mem_image.mp hB
    obtain ⟨C', hC', rfl⟩ := mem_image.mp hC
    have hBC' : B' ≠ C' := fun h => hBC (congrArg (fun C => C.map e) h)
    refine mem_image.mpr ⟨insert (B' ∪ C') F,
      ADR11.mem_merges.mpr ⟨B', hB', C', hC', hBC', rfl⟩, ?_⟩
    rw [forestEmbed_insert, map_union]
    exact he.symm
  · intro hG
    obtain ⟨H, hH, rfl⟩ := mem_image.mp hG
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hH
    rw [forestEmbed_insert, map_union]
    apply ADR11.mem_merges.mpr
    refine ⟨B.map e, ?_, C.map e, ?_, ?_, rfl⟩
    · rw [roots_forestEmbed]
      exact mem_image.mpr ⟨B, hB, rfl⟩
    · rw [roots_forestEmbed]
      exact mem_image.mpr ⟨C, hC, rfl⟩
    · exact fun he => hBC (map_injective e he)
theorem card_roots_forestEmbed {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (F : Finset (Finset L)) :
    (ADR11.roots (forestEmbed e F)).card = (ADR11.roots F).card := by
  rw [roots_forestEmbed]
  exact card_image_of_injective _ (map_injective e)
end Rhone.Coalescent
