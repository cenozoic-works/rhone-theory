/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanHistoryTopology
/-! # Number of mergers of two roots contained in a labelled subset of a forest -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem card_merges_within {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L) :
    ((ADR11.merges F).filter (fun G => ∀ C ∈ G \ F, C ⊆ A)).card =
      (((ADR11.roots F).filter (fun C => C ⊆ A)).card).choose 2 := by
  let S := (ADR11.roots F).filter (fun C => C ⊆ A)
  have hs : S ⊆ F := fun C hC => ADR11.roots_subset F (mem_filter.mp hC).1
  have hSr : ADR11.roots S = S := by
    apply subset_antisymm (ADR11.roots_subset S)
    intro C hC
    refine ADR11.mem_roots.mpr ⟨hC, ?_⟩
    intro D hD hCD
    exact (ADR11.mem_roots.mp (mem_filter.mp hC).1).2 D (hs hD) hCD
  have hSf : ADR11.IsForest S :=
    ⟨fun C hC => hF.1 C (hs hC), fun C hC D hD => hF.2 C (hs hC) D (hs hD)⟩
  have hcount := hSf.card_merges
  rw [hSr] at hcount
  change _ = S.card.choose 2
  rw [← hcount]
  symm
  apply card_bij (fun G _ => G ∪ F)
  · intro G hG
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hG
    rw [hSr] at hB hC
    obtain ⟨hBr, hBA⟩ := mem_filter.mp hB
    obtain ⟨hCr, hCA⟩ := mem_filter.mp hC
    have hu : (insert (B ∪ C) S) ∪ F = insert (B ∪ C) F := by
      rw [insert_union, union_eq_right.mpr hs]
    rw [hu]
    apply mem_filter.mpr
    refine ⟨ADR11.mem_merges.mpr ⟨B, hBr, C, hCr, hBC, rfl⟩, ?_⟩
    intro D hD
    obtain ⟨hD, hDF⟩ := mem_sdiff.mp hD
    rcases mem_insert.mp hD with rfl | hD
    · exact union_subset hBA hCA
    · exact (hDF hD).elim
  · intro G hG H hH he
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hG
    obtain ⟨D, hD, E, hE, hDE, rfl⟩ := ADR11.mem_merges.mp hH
    rw [hSr] at hB hC hD hE
    have hU := ADR11.union_not_mem_of_mem_roots
      (mem_filter.mp hB).1 (mem_filter.mp hC).1 hBC
    have hv : B ∪ C = D ∪ E := by
      have hm : B ∪ C ∈ (insert (D ∪ E) S) ∪ F := he ▸ mem_union_left F (mem_insert_self _ _)
      rw [insert_union, union_eq_right.mpr hs] at hm
      rcases mem_insert.mp hm with hm | hm
      · exact hm
      · exact (hU hm).elim
    rw [hv]
  · intro G hG
    obtain ⟨hGm, hGa⟩ := mem_filter.mp hG
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hGm
    have hU := ADR11.union_not_mem_of_mem_roots hB hC hBC
    have hUA : B ∪ C ⊆ A := hGa _ (mem_sdiff.mpr ⟨mem_insert_self _ _, hU⟩)
    have hBS : B ∈ S := mem_filter.mpr ⟨hB, subset_union_left.trans hUA⟩
    have hCS : C ∈ S := mem_filter.mpr ⟨hC, subset_union_right.trans hUA⟩
    refine ⟨insert (B ∪ C) S, ADR11.mem_merges.mpr ⟨B, ?_, C, ?_, hBC, rfl⟩, ?_⟩
    · rwa [hSr]
    · rwa [hSr]
    · rw [insert_union, union_eq_right.mpr hs]
end Rhone.Combinatorics
