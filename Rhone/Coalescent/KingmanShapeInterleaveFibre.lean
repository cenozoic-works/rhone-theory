/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeInterleaveInverse
/-!
# Subtree interleavings satisfy all separated-history fibre conditions

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem sumPureForest_embed_union {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (F : Finset (Finset L)) (H : Finset (Finset M)) :
    SumPureForest (forestEmbed Function.Embedding.inl F ∪
      forestEmbed Function.Embedding.inr H) := by
  intro C hC
  rcases mem_union.mp hC with hL | hR
  · obtain ⟨A, _, rfl⟩ := mem_image.mp hL
    apply Or.inl
    intro x hx
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx
    exact mem_map.mpr ⟨y, mem_univ _, rfl⟩
  · obtain ⟨A, _, rfl⟩ := mem_image.mp hR
    apply Or.inr
    intro x hx
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx
    exact mem_map.mpr ⟨y, mem_univ _, rfl⟩
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def separatedHistoryInterleave {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (p : (Combinatorics.RankedForestHistory F a × Combinatorics.RankedForestHistory H b) ×
        Combinatorics.HistoryInterleaving a
        b) :
    SeparatedForestHistory F H a b := by
  refine ⟨historyInterleave F H hF hH a b p.1.1 p.1.2 p.2, ?_, ?_, ?_⟩
  · intro k hk
    rw [historyAt_historyInterleave F H hF hH a b p.1.1 p.1.2 p.2 k hk]
    exact sumPureForest_embed_union _ _
  · rw [historyEnd_historyInterleave]
    have hh := historyAt_isForest H hH b p.1.2 b
    rw [historyAt_terminal] at hh
    dsimp only [sumLeftForest]
    rw [history_sum_left_projection _ _ hh]
    have hc := historyAt_root_count F hF a p.1.1 a le_rfl
    rwa [historyAt_terminal] at hc
  · rw [historyEnd_historyInterleave]
    have hf := historyAt_isForest F hF a p.1.1 a
    rw [historyAt_terminal] at hf
    dsimp only [sumRightForest]
    rw [history_sum_right_projection _ _ hf]
    have hc := historyAt_root_count H hH b p.1.2 b le_rfl
    rwa [historyAt_terminal] at hc
end Rhone.Coalescent
