/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeSeparatedProjection
/-! # Inserting clades changes exactly their own subtree restriction -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem sumLeftForest_insert_left {L M : Type*} [Fintype L]
    [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (D : Finset L) :
    sumLeftForest (insert (D.map (Function.Embedding.inl : L ↪ L ⊕ M)) W) =
      insert D (sumLeftForest W) := by
  have hD : D.map (Function.Embedding.inl : L ↪ L ⊕ M) ⊆
      (univ : Finset L).map (Function.Embedding.inl : L ↪ L ⊕ M) :=
    map_subset_map.mpr (subset_univ _)
  simp only [sumLeftForest, filter_insert, ite_eq_left hD, forestPreimage, image_insert,
    preimage_map]
theorem sumRightForest_insert_right {L M : Type*} [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (D : Finset M) :
    sumRightForest (insert (D.map (Function.Embedding.inr : M ↪ L ⊕ M)) W) =
      insert D (sumRightForest W) := by
  have hD : D.map (Function.Embedding.inr : M ↪ L ⊕ M) ⊆
      (univ : Finset M).map (Function.Embedding.inr : M ↪ L ⊕ M) :=
    map_subset_map.mpr (subset_univ _)
  simp only [sumRightForest, filter_insert, ite_eq_left hD, forestPreimage, image_insert,
    preimage_map]
theorem sumRightForest_insert_left {L M : Type*} [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (D : Finset L) (hD : D.Nonempty) :
    sumRightForest (insert (D.map (Function.Embedding.inl : L ↪ L ⊕ M)) W) = sumRightForest W := by
  have hn : ¬ D.map (Function.Embedding.inl : L ↪ L ⊕ M) ⊆
      (univ : Finset M).map (Function.Embedding.inr : M ↪ L ⊕ M) := by
    intro hd
    obtain ⟨d, hdD⟩ := hD
    have hm := hd (mem_map.mpr ⟨d, hdD, rfl⟩)
    obtain ⟨m, _, he⟩ := mem_map.mp hm
    cases he
  simp only [sumRightForest, filter_insert, ite_eq_right hn]
theorem sumLeftForest_insert_right {L M : Type*} [Fintype L]
    [DecidableEq L] [DecidableEq M]
    (W : Finset (Finset (L ⊕ M))) (D : Finset M) (hD : D.Nonempty) :
    sumLeftForest (insert (D.map (Function.Embedding.inr : M ↪ L ⊕ M)) W) = sumLeftForest W := by
  have hn : ¬ D.map (Function.Embedding.inr : M ↪ L ⊕ M) ⊆
      (univ : Finset L).map (Function.Embedding.inl : L ↪ L ⊕ M) := by
    intro hd
    obtain ⟨d, hdD⟩ := hD
    have hm := hd (mem_map.mpr ⟨d, hdD, rfl⟩)
    obtain ⟨m, _, he⟩ := mem_map.mp hm
    cases he
  simp only [sumLeftForest, filter_insert, ite_eq_right hn]
end Rhone.Coalescent
