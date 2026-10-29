/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootSplit
/-! # A binary endpoint has two complementary maximal proper clades -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem binary_hierarchy_root_pair {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) (hG : ADR11.IsBinaryHierarchy G)
    (hL : 2 ≤ Fintype.card L) :
    ∃ A : Finset L, A.Nonempty ∧ (univ \ A).Nonempty ∧
      ADR11.roots (G.erase univ) = {A, univ \ A} := by
  obtain ⟨B, hB, C, hC, hd, hu⟩ := hG.2 univ hG.1.1 (by simpa using hL)
  have hBn := hG.1.2.2.1 B hB
  have hCn := hG.1.2.2.1 C hC
  have hBc : univ \ B = C := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ B ∪ C := by rw [hu]; exact mem_univ x
      exact (mem_union.mp hxU).resolve_left (mem_sdiff.mp hx).2
    · intro hx
      exact mem_sdiff.mpr ⟨mem_univ x, fun hb => disjoint_left.mp hd hb hx⟩
  have hBu : B ≠ univ := by
    intro he
    obtain ⟨x, hx⟩ := hCn
    exact disjoint_left.mp hd (he.symm ▸ mem_univ x) hx
  have hCu : C ≠ univ := by
    intro he
    obtain ⟨x, hx⟩ := hBn
    exact disjoint_left.mp hd hx (he.symm ▸ mem_univ x)
  have hBC : B ≠ C := by
    intro he
    obtain ⟨x, hx⟩ := hBn
    exact disjoint_left.mp hd hx (he ▸ hx)
  have hcases : ∀ D ∈ G.erase univ, D ⊆ B ∨ D ⊆ C := by
    intro D hD
    obtain ⟨hDu, hDG⟩ := mem_erase.mp hD
    rcases ADR11.counts_subset_union_cases hG.1 hB hC hd hDG
      (by rw [hu]; exact subset_univ D) with he | he | he
    · exact (hDu (he.trans hu)).elim
    · exact Or.inl he
    · exact Or.inr he
  have hBr : B ∈ ADR11.roots (G.erase univ) := by
    apply ADR11.mem_roots.mpr
    refine ⟨mem_erase.mpr ⟨hBu, hB⟩, ?_⟩
    intro D hD hBD
    rcases hcases D hD with hDB | hDC
    · exact subset_antisymm hDB hBD
    · obtain ⟨x, hx⟩ := hBn
      exact (disjoint_left.mp hd hx (hDC (hBD hx))).elim
  have hCr : C ∈ ADR11.roots (G.erase univ) := by
    apply ADR11.mem_roots.mpr
    refine ⟨mem_erase.mpr ⟨hCu, hC⟩, ?_⟩
    intro D hD hCD
    rcases hcases D hD with hDB | hDC
    · obtain ⟨x, hx⟩ := hCn
      exact (disjoint_left.mp hd (hDB (hCD hx)) hx).elim
    · exact subset_antisymm hDC hCD
  refine ⟨B, hBn, hBc.symm ▸ hCn, ?_⟩
  rw [hBc]
  ext D
  constructor
  · intro hD
    rcases hcases D (ADR11.roots_subset _ hD) with hDB | hDC
    · have he := (ADR11.mem_roots.mp hD).2 B (mem_erase.mpr ⟨hBu, hB⟩) hDB
      rw [he]; exact mem_insert_self _ _
    · have he := (ADR11.mem_roots.mp hD).2 C (mem_erase.mpr ⟨hCu, hC⟩) hDC
      rw [he]; exact mem_insert_of_mem (mem_singleton_self _)
  · intro hD
    rcases mem_insert.mp hD with rfl | hD
    · exact hBr
    · exact mem_singleton.mp hD ▸ hCr
end Rhone.Coalescent
