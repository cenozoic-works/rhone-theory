/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanColoredRoots
/-! # Pure coloured forests partition their nonempty current roots -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem roots_color_partition
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A) :
    ADR11.roots F = (ADR11.roots F).filter (fun C => C ⊆ A) ∪
      (ADR11.roots F).filter (fun C => C ⊆ univ \ A) ∧
    Disjoint ((ADR11.roots F).filter (fun C => C ⊆ A))
      ((ADR11.roots F).filter (fun C => C ⊆ univ \ A)) := by
  constructor
  · ext C
    simp only [mem_union, mem_filter]
    constructor
    · intro hC
      rcases hpure C (ADR11.roots_subset F hC) with ha | hb
      · exact Or.inl ⟨hC, ha⟩
      · exact Or.inr ⟨hC, hb⟩
    · rintro (h | h) <;> exact h.1
  · apply disjoint_left.mpr
    intro C hCa hCb
    obtain ⟨hCr, hCA⟩ := mem_filter.mp hCa
    have hCB := (mem_filter.mp hCb).2
    obtain ⟨x, hx⟩ := hF.1 C (ADR11.roots_subset F hCr)
    exact (mem_sdiff.mp (hCB hx)).2 (hCA hx)

theorem colored_roots_positive
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hcov : ADR11.lineages F = univ)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A) :
    0 < ((ADR11.roots F).filter (fun C => C ⊆ A)).card ∧
      0 < ((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card := by
  constructor
  · obtain ⟨x, hx⟩ := hA
    have hxl : x ∈ ADR11.lineages F := by rw [hcov]; exact mem_univ x
    obtain ⟨R, hR, hxR⟩ := ADR11.exists_mem_roots_of_mem_lineages hxl
    rw [(roots_color_partition F hF A hpure).1] at hR
    rcases mem_union.mp hR with ha | hb
    · exact card_pos.mpr ⟨R, ha⟩
    · exact ((mem_sdiff.mp ((mem_filter.mp hb).2 hxR)).2 hx).elim
  · obtain ⟨x, hx⟩ := hAc
    have hxl : x ∈ ADR11.lineages F := by rw [hcov]; exact mem_univ x
    obtain ⟨R, hR, hxR⟩ := ADR11.exists_mem_roots_of_mem_lineages hxl
    rw [(roots_color_partition F hF A hpure).1] at hR
    rcases mem_union.mp hR with ha | hb
    · exact ((mem_sdiff.mp hx).2 ((mem_filter.mp ha).2 hxR)).elim
    · exact card_pos.mpr ⟨R, hb⟩
theorem two_color_roots_eq_pair
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (A : Finset L)
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hcov : ADR11.lineages F = univ)
    (hpure : ∀ C ∈ F, C ⊆ A ∨ C ⊆ univ \ A)
    (hk : (ADR11.roots F).card = 2) : ADR11.roots F = {A, univ \ A} := by
  obtain ⟨hpart, hd⟩ := roots_color_partition F hF A hpure
  obtain ⟨hapos, hbpos⟩ := colored_roots_positive F hF A hA hAc hcov hpure
  have hsum := congrArg Finset.card hpart
  rw [card_union_of_disjoint hd, hk] at hsum
  have ha1 : ((ADR11.roots F).filter (fun C => C ⊆ A)).card = 1 := by omega
  have hb1 : ((ADR11.roots F).filter (fun C => C ⊆ univ \ A)).card = 1 := by omega
  obtain ⟨B, hB⟩ := card_eq_one.mp ha1
  obtain ⟨C, hC⟩ := card_eq_one.mp hb1
  have hBm : B ∈ (ADR11.roots F).filter (fun C => C ⊆ A) := by rw [hB]; simp
  have hCm : C ∈ (ADR11.roots F).filter (fun C => C ⊆ univ \ A) := by rw [hC]; simp
  have hBA := (mem_filter.mp hBm).2
  have hCA := (mem_filter.mp hCm).2
  have hr : ADR11.roots F = {B, C} := by simpa only [hB, hC, singleton_union] using hpart
  have hBC : B ∪ C = univ := by
    calc
      _ = ADR11.lineages {B, C} := by simp [ADR11.lineages]
      _ = ADR11.lineages (ADR11.roots F) := by rw [hr]
      _ = ADR11.lineages F := ADR11.lineages_roots
      _ = univ := hcov
  have hBe : B = A := by
    apply subset_antisymm hBA
    intro x hx
    have hxU : x ∈ B ∪ C := by rw [hBC]; exact mem_univ x
    rcases mem_union.mp hxU with hb | hc
    · exact hb
    · exact ((mem_sdiff.mp (hCA hc)).2 hx).elim
  have hCe : C = univ \ A := by
    apply subset_antisymm hCA
    intro x hx
    have hxU : x ∈ B ∪ C := by rw [hBC]; exact mem_univ x
    rcases mem_union.mp hxU with hb | hc
    · exact ((mem_sdiff.mp hx).2 (hBA hb)).elim
    · exact hc
  rwa [hBe, hCe] at hr
end Rhone.Combinatorics
