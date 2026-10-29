/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeSeparatedProjection
/-! # Full daughter clades determine the exact projected root count -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem roots_eq_full_clade {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hU : univ ∈ F) : ADR11.roots F = {univ} := by
  ext A
  constructor
  · intro hA
    exact mem_singleton.mpr ((ADR11.mem_roots.mp hA).2 univ hU (subset_univ A)).symm
  · intro hA
    obtain rfl := mem_singleton.mp hA
    exact ADR11.mem_roots.mpr ⟨hU, fun B _ hUB => subset_antisymm (subset_univ B) hUB⟩
theorem sumLeftForest_full_root {L M : Type*} [Fintype L] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M)))
    (hU : (univ : Finset L).map Function.Embedding.inl ∈ W) :
    (ADR11.roots (sumLeftForest W)).card = 1 := by
  have hleft : univ ∈ sumLeftForest W :=
    mem_image.mpr ⟨univ.map Function.Embedding.inl, mem_filter.mpr ⟨hU, subset_rfl⟩,
      preimage_map Function.Embedding.inl univ⟩
  rw [roots_eq_full_clade _ hleft, card_singleton]
theorem sumRightForest_full_root {L M : Type*} [Fintype M] [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M)))
    (hU : (univ : Finset M).map Function.Embedding.inr ∈ W) :
    (ADR11.roots (sumRightForest W)).card = 1 := by
  have hright : univ ∈ sumRightForest W :=
    mem_image.mpr ⟨univ.map Function.Embedding.inr, mem_filter.mpr ⟨hU, subset_rfl⟩,
      preimage_map Function.Embedding.inr univ⟩
  rw [roots_eq_full_clade _ hright, card_singleton]
end Rhone.Coalescent
