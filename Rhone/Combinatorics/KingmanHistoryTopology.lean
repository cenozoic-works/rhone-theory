/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanHistories
/-! # Chronological forest histories terminate in binary labelled topologies -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem historyEnd_spec {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (h : RankedForestHistory F t) :
    ADR11.IsForest (historyEnd F t h) ∧
      (ADR11.roots (historyEnd F t h)).card + t = (ADR11.roots F).card ∧
      F ⊆ historyEnd F t h ∧ ADR11.lineages (historyEnd F t h) = ADR11.lineages F := by
  induction t generalizing F with
  | zero => exact ⟨hF, by simp [historyEnd], subset_rfl, rfl⟩
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    obtain ⟨hG, hc, hs, -, hl⟩ := hF.of_mem_merges G.2
    obtain ⟨hE, hEc, hEs, hEl⟩ := ih G.1 hG h
    exact ⟨hE, by change (ADR11.roots (historyEnd G.1 t h)).card + (t + 1) = _; omega,
      hs.trans hEs, hEl.trans hl⟩
private def binaryClades {L : Type*} [DecidableEq L] (F : Finset (Finset L)) : Prop :=
  ∀ A ∈ F, 2 ≤ A.card → ∃ B ∈ F, ∃ C ∈ F, Disjoint B C ∧ B ∪ C = A
private theorem binaryClades_merge {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (hb : binaryClades F)
    (G : Finset (Finset L)) (hG : G ∈ ADR11.merges F) : binaryClades G := by
  obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hG
  intro A hA hAc
  rcases mem_insert.mp hA with rfl | hA
  · exact ⟨B, mem_insert_of_mem (ADR11.roots_subset F hB), C,
      mem_insert_of_mem (ADR11.roots_subset F hC), hF.disjoint_of_mem_roots hB hC hBC, rfl⟩
  · obtain ⟨B', hB', C', hC', hd, hu⟩ := hb A hA hAc
    exact ⟨B', mem_insert_of_mem hB', C', mem_insert_of_mem hC', hd, hu⟩
private theorem historyEnd_binaryClades {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (hb : binaryClades F)
    (t : ℕ) (h : RankedForestHistory F t) : binaryClades (historyEnd F t h) := by
  induction t generalizing F with
  | zero => exact hb
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    exact ih G.1 (hF.of_mem_merges G.2).1 (binaryClades_merge F hF hb G.1 G.2) h

theorem historyEnd_isBinaryHierarchy (n : ℕ) (hn : 1 ≤ n)
    (h : RankedLabelledHistory n) :
    ADR11.IsBinaryHierarchy (historyEnd (ADR11.singletonForest n) (n - 1) h) := by
  obtain ⟨hE, hc, hs, hl⟩ := historyEnd_spec _ (ADR11.isForest_singletonForest n) _ h
  rw [ADR11.card_roots_singletonForest] at hc
  have hroot : (ADR11.roots (historyEnd (ADR11.singletonForest n) (n - 1) h)).card = 1 :=
    by omega
  have hlineages : ADR11.lineages (ADR11.singletonForest n) = univ := by
    ext x
    simp [ADR11.lineages, ADR11.singletonForest]
  have hfull : univ ∈ historyEnd (ADR11.singletonForest n) (n - 1) h := by
    have hm := ADR11.lineages_mem_of_card_roots_eq_one hroot
    rwa [hl, hlineages] at hm
  have hsingle : ∀ x : Fin n, {x} ∈ historyEnd (ADR11.singletonForest n) (n - 1) h := by
    intro x
    apply hs
    simp [ADR11.singletonForest]
  refine ⟨⟨hfull, hsingle, hE⟩, historyEnd_binaryClades _
    (ADR11.isForest_singletonForest n) ?_ _ h⟩
  intro A hA hAc
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hA
  simp at hAc
end Rhone.Combinatorics
