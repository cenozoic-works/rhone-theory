/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootOrientation
/-! # First mergers restricted to a pure leaf-set side -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem roots_within_pure_forest {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A) :
    ADR11.roots (F.filter (fun C => C ⊆ A)) = (ADR11.roots F).filter (fun C => C ⊆ A) := by
  ext C
  constructor
  · intro hC
    obtain ⟨hCm, hmax⟩ := ADR11.mem_roots.mp hC
    obtain ⟨hCF, hCA⟩ := mem_filter.mp hCm
    apply mem_filter.mpr
    refine ⟨ADR11.mem_roots.mpr ⟨hCF, ?_⟩, hCA⟩
    intro D hD hCD
    rcases hpure D hD with hDA | hDA
    · exact hmax D (mem_filter.mpr ⟨hD, hDA⟩) hCD
    · obtain ⟨x, hx⟩ := hF.1 C hCF
      exact ((mem_sdiff.mp (hDA (hCD hx))).2 (hCA hx)).elim
  · intro hC
    obtain ⟨hCr, hCA⟩ := mem_filter.mp hC
    obtain ⟨hCm, hmax⟩ := ADR11.mem_roots.mp hCr
    apply ADR11.mem_roots.mpr
    refine ⟨mem_filter.mpr ⟨hCm, hCA⟩, ?_⟩
    intro D hD hCD
    exact hmax D (mem_filter.mp hD).1 hCD
theorem sum_merges_within_restrict {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A)
    (f : Finset (Finset L) → ℝ) :
    (∑ G ∈ (ADR11.merges F).filter (fun G => ∀ C ∈ G \ F, C ⊆ A),
      f (G.filter (fun C => C ⊆ A))) =
      ∑ H ∈ ADR11.merges (F.filter (fun C => C ⊆ A)), f H := by
  classical
  let S := F.filter (fun C => C ⊆ A)
  have hs : S ⊆ F := filter_subset _ _
  have hSr : ADR11.roots S = (ADR11.roots F).filter (fun C => C ⊆ A) :=
    roots_within_pure_forest F hF A hpure
  have hrecover : ∀ H ∈ ADR11.merges S, (H ∪ F).filter (fun C => C ⊆ A) = H := by
    intro H hH
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hH
    rw [hSr] at hB hC
    have hUA := union_subset (mem_filter.mp hB).2 (mem_filter.mp hC).2
    rw [insert_union, union_eq_right.mpr hs, filter_insert, ite_eq_left hUA]
  symm
  change (∑ H ∈ ADR11.merges S, f H) = _
  apply sum_bij (fun H _ => H ∪ F)
  · intro H hH
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hH
    rw [hSr] at hB hC
    obtain ⟨hBr, hBA⟩ := mem_filter.mp hB
    obtain ⟨hCr, hCA⟩ := mem_filter.mp hC
    rw [insert_union, union_eq_right.mpr hs]
    apply mem_filter.mpr
    refine ⟨ADR11.mem_merges.mpr ⟨B, hBr, C, hCr, hBC, rfl⟩, ?_⟩
    intro D hD
    obtain ⟨hD, hn⟩ := mem_sdiff.mp hD
    rcases mem_insert.mp hD with rfl | hD
    · exact union_subset hBA hCA
    · exact (hn hD).elim
  · intro H hH J hJ he
    have hh := congrArg (fun G : Finset (Finset L) => G.filter (fun C => C ⊆ A)) he
    rwa [hrecover H hH, hrecover J hJ] at hh
  · intro G hG
    obtain ⟨hGm, hGa⟩ := mem_filter.mp hG
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hGm
    have hU := ADR11.union_not_mem_of_mem_roots hB hC hBC
    have hUA := hGa (B ∪ C) (mem_sdiff.mpr ⟨mem_insert_self _ _, hU⟩)
    refine ⟨insert (B ∪ C) S, ADR11.mem_merges.mpr ⟨B, ?_, C, ?_, hBC, rfl⟩, ?_⟩
    · rw [hSr]
      exact mem_filter.mpr ⟨hB, subset_union_left.trans hUA⟩
    · rw [hSr]
      exact mem_filter.mpr ⟨hC, subset_union_right.trans hUA⟩
    · rw [insert_union, union_eq_right.mpr hs]
  · intro H hH
    rw [hrecover H hH]
end Rhone.Coalescent
