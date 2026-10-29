/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanColoredMerges
/-! # Coloured root-count changes and cross-colour merger support -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem card_roots_within_merge
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A B C : Finset L)
    (hB : B ∈ ADR11.roots F) (hC : C ∈ ADR11.roots F) (hBC : B ≠ C)
    (hBA : B ⊆ A) (hCA : C ⊆ A) :
    ((ADR11.roots (insert (B ∪ C) F)).filter (fun D => D ⊆ A)).card + 1 =
      ((ADR11.roots F).filter (fun D => D ⊆ A)).card := by
  have hU : B ∪ C ∉ (((ADR11.roots F).filter (fun D => D ⊆ A)).erase B).erase C := by
    intro hu
    exact ADR11.union_not_mem_of_mem_roots hB hC hBC
      (ADR11.roots_subset F (mem_filter.mp (mem_of_mem_erase (mem_of_mem_erase hu))).1)
  have hBm : B ∈ (ADR11.roots F).filter (fun D => D ⊆ A) := mem_filter.mpr ⟨hB, hBA⟩
  have hCm : C ∈ ((ADR11.roots F).filter (fun D => D ⊆ A)).erase B :=
    mem_erase.mpr ⟨hBC.symm, mem_filter.mpr ⟨hC, hCA⟩⟩
  rw [hF.roots_merge hB hC hBC]
  simp only [filter_insert, union_subset_iff, hBA, hCA, and_self, ite_true, filter_erase]
  rw [card_insert_of_notMem hU, card_erase_add_one hCm, card_erase_add_one hBm]

theorem roots_within_merge_outside
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A B C : Finset L)
    (hB : B ∈ ADR11.roots F) (hC : C ∈ ADR11.roots F) (hBC : B ≠ C)
    (hBA : ¬B ⊆ A) (hCA : ¬C ⊆ A) :
    (ADR11.roots (insert (B ∪ C) F)).filter (fun D => D ⊆ A) =
      (ADR11.roots F).filter (fun D => D ⊆ A) := by
  rw [hF.roots_merge hB hC hBC]
  simp only [filter_insert, union_subset_iff, hBA, hCA, false_and, ite_false, filter_erase]
  have hBn : B ∉ (ADR11.roots F).filter (fun D => D ⊆ A) :=
    fun h => hBA (mem_filter.mp h).2
  have hCn : C ∉ (ADR11.roots F).filter (fun D => D ⊆ A) :=
    fun h => hCA (mem_filter.mp h).2
  rw [erase_eq_of_notMem hBn, erase_eq_of_notMem hCn]
theorem merge_union_ne_univ_of_three_roots
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (B C : Finset L)
    (hB : B ∈ ADR11.roots F) (hC : C ∈ ADR11.roots F) (hBC : B ≠ C)
    (hk : 3 ≤ (ADR11.roots F).card) : B ∪ C ≠ univ := by
  have hCm : C ∈ (ADR11.roots F).erase B := mem_erase.mpr ⟨hBC.symm, hC⟩
  have hc1 := card_erase_add_one hB
  have hc2 := card_erase_add_one hCm
  have hpos : 0 < (((ADR11.roots F).erase B).erase C).card := by omega
  obtain ⟨R, hR⟩ := card_pos.mp hpos
  obtain ⟨hRC, hR'⟩ := mem_erase.mp hR
  obtain ⟨hRB, hRr⟩ := mem_erase.mp hR'
  obtain ⟨x, hx⟩ := hF.1 R (ADR11.roots_subset F hRr)
  intro hu
  have hxU : x ∈ B ∪ C := by rw [hu]; exact mem_univ x
  rcases mem_union.mp hxU with hxB | hxC
  · exact disjoint_left.mp (hF.disjoint_of_mem_roots hRr hB hRB) hx hxB
  · exact disjoint_left.mp (hF.disjoint_of_mem_roots hRr hC hRC) hx hxC
end Rhone.Combinatorics
