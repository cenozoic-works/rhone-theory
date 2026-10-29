/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootPair
/-! # Endpoint sample-root event decomposition into root child clades -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem root_pair_sample_indicator {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) (hG : ADR11.IsBinaryHierarchy G)
    (hL : 2 ≤ Fintype.card L) (S : Finset L) (hS : S.Nonempty) :
    (if ((ADR11.roots (G.erase univ)).filter
      (fun R => ¬Disjoint R S)).card = 2 then (1 : ℝ) else 0) =
    1 - ∑ A ∈ (univ : Finset (Finset L)).erase univ,
      if S ⊆ A then
        (if ADR11.roots (G.erase univ) = {A, univ \ A} then (1 : ℝ) else 0)
      else 0 := by
  classical
  obtain ⟨B, hB, hBc, hr⟩ := binary_hierarchy_root_pair G hG hL
  have hBu : B ≠ univ := by
    intro he
    simp [he] at hBc
  have hCu : univ \ B ≠ univ := by
    intro he
    obtain ⟨x, hx⟩ := hB
    have hxC : x ∈ univ \ B := he.symm ▸ mem_univ x
    exact (mem_sdiff.mp hxC).2 hx
  have hBC : B ≠ univ \ B := by
    intro he
    obtain ⟨x, hx⟩ := hB
    exact (mem_sdiff.mp (he ▸ hx)).2 hx
  have hcc : univ \ (univ \ B) = B := by ext x; simp
  have hevent : ∀ A : Finset L,
      ADR11.roots (G.erase univ) = {A, univ \ A} ↔ A ∈ ({B, univ \ B} : Finset (Finset L)) := by
    intro A
    constructor
    · intro he
      rw [← hr, he]
      exact mem_insert_self _ _
    · intro hA
      rcases mem_insert.mp hA with rfl | hA
      · exact hr
      · have he := mem_singleton.mp hA
        rw [he, hcc, pair_comm]
        exact hr
  have hsum : (∑ A ∈ (univ : Finset (Finset L)).erase univ,
      if S ⊆ A then
        (if ADR11.roots (G.erase univ) = {A, univ \ A} then (1 : ℝ) else 0)
      else 0) = (if S ⊆ B then (1 : ℝ) else 0) +
        (if S ⊆ univ \ B then (1 : ℝ) else 0) := by
    simp_rw [hevent]
    have hsub : {B, univ \ B} ⊆ (univ : Finset (Finset L)).erase univ := by
      intro A hA
      rcases mem_insert.mp hA with rfl | hA
      · exact mem_erase.mpr ⟨hBu, mem_univ _⟩
      · have he := mem_singleton.mp hA
        rw [he]
        exact mem_erase.mpr ⟨hCu, mem_univ _⟩
    rw [← sum_subset hsub (by
      intro A hA hAn
      simp only [hAn, ite_false, ite_self])]
    rw [sum_pair hBC]
    simp
  have hdB : Disjoint B S ↔ S ⊆ univ \ B := by
    constructor
    · intro hd x hx
      exact mem_sdiff.mpr ⟨mem_univ x, fun hb => disjoint_left.mp hd hb hx⟩
    · intro hs
      apply disjoint_left.mpr
      intro x hxB hxS
      exact (mem_sdiff.mp (hs hxS)).2 hxB
  have hdC : Disjoint (univ \ B) S ↔ S ⊆ B := by
    constructor
    · intro hd x hx
      by_contra hxb
      exact disjoint_left.mp hd (mem_sdiff.mpr ⟨mem_univ x, hxb⟩) hx
    · intro hs
      apply disjoint_left.mpr
      intro x hxC hxS
      exact (mem_sdiff.mp hxC).2 (hs hxS)
  have hnotboth : ¬(S ⊆ B ∧ S ⊆ univ \ B) := by
    rintro ⟨ha, hb⟩
    obtain ⟨x, hx⟩ := hS
    exact (mem_sdiff.mp (hb hx)).2 (ha hx)
  rw [hsum, hr]
  by_cases ha : S ⊆ B <;> by_cases hb : S ⊆ univ \ B
  · exact (hnotboth ⟨ha, hb⟩).elim
  · simp [filter_insert, filter_singleton, ha, hb, hdB, hdC]
  · simp [filter_insert, filter_singleton, ha, hb, hdB, hdC]
  · simp [filter_insert, filter_singleton, ha, hb, hdB, hdC, hBC]
end Rhone.Coalescent
