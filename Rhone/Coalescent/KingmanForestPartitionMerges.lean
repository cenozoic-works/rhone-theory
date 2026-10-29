/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import ADR11.Coalescent.Forest
public import Rhone.Coalescent.KingmanPartition

/-!
# Forest merges and partition merges

Uses `lean4-adr11` by The-Anh Vu-Le. -/

@[expose] public section

namespace Rhone.Coalescent.External.ADR11

open Finset _root_.ADR11

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {F : Finset (Finset L)} {π σ : Finpartition (univ : Finset L)}

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem roots_merge_eq_parts_mergeBlocks (hF : IsForest F) (hπ : π.parts = roots F)
    {A B : Finset L} (hA : A ∈ roots F) (hB : B ∈ roots F) (hne : A ≠ B) :
    roots (insert (A ∪ B) F) = (mergeBlocks π {A, B}).parts := by
  have hs : ({A, B} : Finset (Finset L)) ⊆ π.parts := by
    simp only [insert_subset_iff, singleton_subset_iff, hπ]
    exact ⟨hA, hB⟩
  rw [hF.roots_merge hA hB hne, parts_mergeBlocks hs (by simp)]
  simp only [sup_insert, sup_singleton, id_eq, sup_eq_union]
  congr 1
  ext C
  simp [hπ, and_assoc, and_comm, and_left_comm]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem roots_eq_parts_of_mem_merges (hF : IsForest F) (hπ : π.parts = roots F)
    {G : Finset (Finset L)} (hG : G ∈ _root_.ADR11.merges F) :
    ∃ τ ∈ Rhone.Coalescent.merges π, roots G = τ.parts := by
  obtain ⟨A, hA, B, hB, hne, rfl⟩ := _root_.ADR11.mem_merges.mp hG
  refine ⟨mergeBlocks π {A, B}, ?_, roots_merge_eq_parts_mergeBlocks hF hπ hA hB hne⟩
  apply mem_image.mpr
  refine ⟨{A, B}, mem_powersetCard.mpr ⟨?_, ?_⟩, rfl⟩
  · simp only [insert_subset_iff, singleton_subset_iff, hπ]
    exact ⟨hA, hB⟩
  · simp [hne]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem exists_merge_roots_eq_of_mem_merges (hF : IsForest F) (hπ : π.parts = roots F)
    (hσ : σ ∈ Rhone.Coalescent.merges π) :
    ∃ G ∈ _root_.ADR11.merges F, roots G = σ.parts := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hσ
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
  obtain ⟨A, B, hne, rfl⟩ := card_eq_two.mp hcard
  have hA : A ∈ roots F := hπ ▸ hsub (by simp)
  have hB : B ∈ roots F := hπ ▸ hsub (by simp)
  refine ⟨insert (A ∪ B) F, ?_, roots_merge_eq_parts_mergeBlocks hF hπ hA hB hne⟩
  exact _root_.ADR11.mem_merges.mpr ⟨A, hA, B, hB, hne, rfl⟩

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem roots_injective_on_merges (hF : IsForest F) (hπ : π.parts = roots F) :
    Set.InjOn roots (_root_.ADR11.merges F : Set (Finset (Finset L))) := by
  intro G hG H hH heq
  obtain ⟨A, hA, B, hB, hAB, rfl⟩ := _root_.ADR11.mem_merges.mp hG
  obtain ⟨C, hC, D, hD, hCD, rfl⟩ := _root_.ADR11.mem_merges.mp hH
  have hs : ({A, B} : Finset (Finset L)) ⊆ π.parts := by
    simp only [insert_subset_iff, singleton_subset_iff, hπ]
    exact ⟨hA, hB⟩
  have ht : ({C, D} : Finset (Finset L)) ⊆ π.parts := by
    simp only [insert_subset_iff, singleton_subset_iff, hπ]
    exact ⟨hC, hD⟩
  have hp : ({A, B} : Finset (Finset L)) = {C, D} := by
    rw [← parts_sdiff_parts_mergeBlocks hs (by simp [hAB]),
      ← parts_sdiff_parts_mergeBlocks ht (by simp [hCD]),
      ← roots_merge_eq_parts_mergeBlocks hF hπ hA hB hAB,
      ← roots_merge_eq_parts_mergeBlocks hF hπ hC hD hCD, heq]
  have hu : A ∪ B = C ∪ D := by
    simpa using congrArg (fun s : Finset (Finset L) => s.sup id) hp
  rw [hu]

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem exists_merge_roots_eq_iff (hF : IsForest F) (hπ : π.parts = roots F) :
    (∃ G ∈ _root_.ADR11.merges F, roots G = σ.parts) ↔ σ ∈ Rhone.Coalescent.merges π := by
  constructor
  · rintro ⟨G, hG, heq⟩
    obtain ⟨τ, hτ, hτroots⟩ := roots_eq_parts_of_mem_merges hF hπ hG
    have hτσ : τ = σ := Finpartition.ext (hτroots.symm.trans heq)
    exact hτσ ▸ hτ
  · exact exists_merge_roots_eq_of_mem_merges hF hπ

/-- Uses `lean4-adr11` by The-Anh Vu-Le. -/
theorem card_merges_filter_roots (hF : IsForest F) (hπ : π.parts = roots F) :
    ((_root_.ADR11.merges F).filter (fun G => roots G = σ.parts)).card =
      if σ ∈ Rhone.Coalescent.merges π then 1 else 0 := by
  by_cases hσ : σ ∈ Rhone.Coalescent.merges π
  · obtain ⟨G, hG, heq⟩ := exists_merge_roots_eq_of_mem_merges hF hπ hσ
    have hf : (_root_.ADR11.merges F).filter (fun H => roots H = σ.parts) = {G} := by
      ext H
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hH, hroots⟩
        exact roots_injective_on_merges hF hπ hH hG (hroots.trans heq.symm)
      · rintro rfl
        exact ⟨hG, heq⟩
    simp [hσ, hf]
  · have hf : (_root_.ADR11.merges F).filter (fun G => roots G = σ.parts) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro G hG hroots
      exact hσ ((exists_merge_roots_eq_iff hF hπ).mp ⟨G, hG, hroots⟩)
    simp [hσ, hf]

end Rhone.Coalescent.External.ADR11
