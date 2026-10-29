/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanForestPreimage
public import Rhone.Combinatorics.KingmanHistoryTopology
/-!
# Join two binary endpoint hierarchies on disjoint sum-tagged leaves

Source: wedderburn1922, §1, pp. 121–122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: wedderburn1922, §1, pp. 121–122. -/
def binaryHierarchyJoin {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (G : Finset (Finset L)) (H : Finset (Finset M)) :
    Finset (Finset (L ⊕ M)) :=
  insert univ (forestEmbed Function.Embedding.inl G ∪
    forestEmbed Function.Embedding.inr H)
private theorem shape_embedded_children {L M : Type*} [Fintype L]
    [DecidableEq L] [DecidableEq M] (e : L ↪ M) (G : Finset (Finset L))
    (hG : ADR11.IsBinaryHierarchy G) (A : Finset M) (hA : A ∈ forestEmbed e G)
    (hAc : 2 ≤ A.card) :
    ∃ B ∈ forestEmbed e G, ∃ C ∈ forestEmbed e G, Disjoint B C ∧ B ∪ C = A := by
  obtain ⟨D, hDG, rfl⟩ := mem_image.mp hA
  obtain ⟨B, hBG, C, hCG, hd, hu⟩ := hG.2 D hDG (by simpa only [card_map] using hAc)
  refine ⟨B.map e, mem_image.mpr ⟨B, hBG, rfl⟩,
    C.map e, mem_image.mpr ⟨C, hCG, rfl⟩, (disjoint_map e).mpr hd, ?_⟩
  rw [← map_union, hu]
/-- Source: wedderburn1922, §1, pp. 121–122. -/
theorem isBinaryHierarchy_join {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (G : Finset (Finset L)) (H : Finset (Finset M))
    (hG : ADR11.IsBinaryHierarchy G) (hH : ADR11.IsBinaryHierarchy H) :
    ADR11.IsBinaryHierarchy (binaryHierarchyJoin G H) := by
  classical
  let e : L ↪ L ⊕ M := Function.Embedding.inl
  let f : M ↪ L ⊕ M := Function.Embedding.inr
  let F := forestEmbed e G ∪ forestEmbed f H
  have hF : ADR11.IsForest F :=
    ((isForest_forestEmbed_iff e G).mpr hG.1.2.2).union
      ((isForest_forestEmbed_iff f H).mpr hH.1.2.2) (by
        intro A hA B hB
        obtain ⟨C, _, rfl⟩ := mem_image.mp hA
        obtain ⟨D, _, rfl⟩ := mem_image.mp hB
        exact Or.inr (Or.inr (Finset.disjoint_map_inl_map_inr C D)))
  have hrootL : (univ : Finset L).map e ∈ F :=
    mem_union_left _ (mem_image.mpr ⟨univ, hG.1.1, rfl⟩)
  have hrootR : (univ : Finset M).map f ∈ F :=
    mem_union_right _ (mem_image.mpr ⟨univ, hH.1.1, rfl⟩)
  have hnonempty : (univ : Finset (L ⊕ M)).Nonempty := by
    obtain ⟨x, _⟩ := hG.1.2.2.1 univ hG.1.1
    exact ⟨Sum.inl x, mem_univ _⟩
  have hIns : ADR11.IsForest (insert univ F) := by
    constructor
    · intro A hA
      rcases mem_insert.mp hA with rfl | hA
      · exact hnonempty
      · exact hF.1 A hA
    · intro A hA B hB
      rcases mem_insert.mp hA with rfl | hA
      · exact Or.inr (Or.inl (subset_univ B))
      · rcases mem_insert.mp hB with rfl | hB
        · exact Or.inl (subset_univ A)
        · exact hF.2 A hA B hB
  change ADR11.IsBinaryHierarchy (insert univ F)
  refine ⟨⟨mem_insert_self _ _, ?_, hIns⟩, ?_⟩
  · intro x
    cases x with
    | inl x =>
      exact mem_insert_of_mem (mem_union_left _
        (mem_image.mpr ⟨{x}, hG.1.2.1 x, map_singleton e x⟩))
    | inr y =>
      exact mem_insert_of_mem (mem_union_right _
        (mem_image.mpr ⟨{y}, hH.1.2.1 y, map_singleton f y⟩))
  · intro A hA hAc
    rcases mem_insert.mp hA with rfl | hA
    · refine ⟨univ.map e, mem_insert_of_mem hrootL,
        univ.map f, mem_insert_of_mem hrootR, Finset.disjoint_map_inl_map_inr univ univ, ?_⟩
      ext x
      cases x <;> simp [e, f]
    · rcases mem_union.mp hA with hA | hA
      · obtain ⟨B, hB, C, hC, hd, hu⟩ := shape_embedded_children e G hG A hA hAc
        exact ⟨B, mem_insert_of_mem (mem_union_left _ hB),
          C, mem_insert_of_mem (mem_union_left _ hC), hd, hu⟩
      · obtain ⟨B, hB, C, hC, hd, hu⟩ := shape_embedded_children f H hH A hA hAc
        exact ⟨B, mem_insert_of_mem (mem_union_right _ hB),
          C, mem_insert_of_mem (mem_union_right _ hC), hd, hu⟩
end Rhone.Coalescent
