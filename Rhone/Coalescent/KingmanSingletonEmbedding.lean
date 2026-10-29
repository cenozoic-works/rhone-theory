/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanSubtreeTopology
/-! # Singleton founder forests under injective leaf-label maps -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem singletonForest_forestEmbed (a n : ℕ) (e : Fin a ↪ Fin n) :
    forestEmbed e (ADR11.singletonForest a) =
      (ADR11.singletonForest n).filter (fun C => C ⊆ (univ : Finset (Fin a)).map e) := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hC
    obtain ⟨x, _, rfl⟩ := mem_image.mp hD
    rw [map_singleton]
    exact mem_filter.mpr ⟨mem_image.mpr ⟨e x, mem_univ _, rfl⟩,
      singleton_subset_iff.mpr (mem_map.mpr ⟨x, mem_univ _, rfl⟩)⟩
  · intro hC
    obtain ⟨hC, hsub⟩ := mem_filter.mp hC
    obtain ⟨y, _, rfl⟩ := mem_image.mp hC
    obtain ⟨x, _, rfl⟩ := mem_map.mp (singleton_subset_iff.mp hsub)
    exact mem_image.mpr ⟨{x}, mem_image.mpr ⟨x, mem_univ _, rfl⟩, map_singleton e x⟩
end Rhone.Coalescent
