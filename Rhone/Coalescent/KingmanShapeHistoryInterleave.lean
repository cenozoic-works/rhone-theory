/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeHistorySumStep
public import Rhone.Combinatorics.KingmanShapeInterleaving
/-!
# Interleave valid subtree histories by chosen chronological merger slots

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem historyAt_terminal {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : Combinatorics.RankedForestHistory F t) :
    Combinatorics.historyAt F t h t = Combinatorics.historyEnd F t h := by
  induction t generalizing F with
  | zero => rfl
  | succ t ih => exact ih h.1.1 h.2
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
def historyInterleaveTrace {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : Combinatorics.RankedForestHistory F a) (g : Combinatorics.RankedForestHistory H b)
    (s : Combinatorics.HistoryInterleaving a b) :
    Combinatorics.ForestMergerTrace
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H) (a + b) := by
  refine ⟨fun k => forestEmbed Function.Embedding.inl
      (Combinatorics.historyAt F a h (Combinatorics.interleavingLeft s k.val)) ∪
    forestEmbed Function.Embedding.inr
        (Combinatorics.historyAt H b g (Combinatorics.interleavingRight s k.val)), ?_, ?_⟩
  · have hz := Combinatorics.interleaving_counts_zero s
    change forestEmbed Function.Embedding.inl
        (Combinatorics.historyAt F a h (Combinatorics.interleavingLeft s 0)) ∪
      forestEmbed Function.Embedding.inr
          (Combinatorics.historyAt H b g (Combinatorics.interleavingRight s 0)) = _
    rw [hz.1, hz.2, Combinatorics.historyAt_zero, Combinatorics.historyAt_zero]
  · intro k
    change forestEmbed Function.Embedding.inl
        (Combinatorics.historyAt F a h (Combinatorics.interleavingLeft s (k.val + 1))) ∪
      forestEmbed Function.Embedding.inr
          (Combinatorics.historyAt H b g (Combinatorics.interleavingRight s (k.val + 1))) ∈
      ADR11.merges (forestEmbed Function.Embedding.inl
          (Combinatorics.historyAt F a h (Combinatorics.interleavingLeft s k.val)) ∪
        forestEmbed Function.Embedding.inr
            (Combinatorics.historyAt H b g (Combinatorics.interleavingRight s k.val)))
    have hc := Combinatorics.interleaving_counts_succ s k
    by_cases hm : k ∈ s.1
    · rw [ite_eq_left hm] at hc
      rw [hc.1, hc.2]
      have hlt : Combinatorics.interleavingLeft s k.val < a := by
        have hb := Combinatorics.interleavingLeft_le s (k.val + 1)
        rw [hc.1] at hb
        omega
      exact history_sum_left_merge _ _ _
        (historyAt_isForest F hF a h _) (Combinatorics.historyAt_next_merge F a h _ hlt)
    · rw [ite_eq_right hm] at hc
      rw [hc.1, hc.2]
      have hlt : Combinatorics.interleavingRight s k.val < b := by
        have hb := Combinatorics.interleavingRight_le s (k.val + 1)
        rw [hc.2] at hb
        omega
      exact history_sum_right_merge _ _ _
        (historyAt_isForest H hH b g _) (Combinatorics.historyAt_next_merge H b g _ hlt)
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def historyInterleave {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : Combinatorics.RankedForestHistory F a) (g : Combinatorics.RankedForestHistory H b)
    (s : Combinatorics.HistoryInterleaving a b) :
    Combinatorics.RankedForestHistory
      (forestEmbed Function.Embedding.inl F ∪ forestEmbed Function.Embedding.inr H) (a + b) :=
  (Combinatorics.rankedForestHistoryTraceEquiv _ _).symm
      (historyInterleaveTrace F H hF hH a b h g s)
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem historyAt_historyInterleave {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : Combinatorics.RankedForestHistory F a) (g : Combinatorics.RankedForestHistory H b)
    (s : Combinatorics.HistoryInterleaving a b) (k : ℕ) (hk : k ≤ a + b) :
    Combinatorics.historyAt _ (a + b) (historyInterleave F H hF hH a b h g s) k =
      forestEmbed Function.Embedding.inl
          (Combinatorics.historyAt F a h (Combinatorics.interleavingLeft s k)) ∪
      forestEmbed Function.Embedding.inr
          (Combinatorics.historyAt H b g (Combinatorics.interleavingRight s k)) := by
  have he := (Combinatorics.rankedForestHistoryTraceEquiv _ (a + b)).apply_symm_apply
    (historyInterleaveTrace F H hF hH a b h g s)
  exact congrFun (congrArg Subtype.val he) ⟨k, by omega⟩
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem historyEnd_historyInterleave {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : Combinatorics.RankedForestHistory F a) (g : Combinatorics.RankedForestHistory H b)
    (s : Combinatorics.HistoryInterleaving a b) :
    Combinatorics.historyEnd _ (a + b) (historyInterleave F H hF hH a b h g s) =
      forestEmbed Function.Embedding.inl (Combinatorics.historyEnd F a h) ∪
      forestEmbed Function.Embedding.inr (Combinatorics.historyEnd H b g) := by
  rw [← historyAt_terminal, historyAt_historyInterleave _ _ _ _ _ _ _ _ _ _ le_rfl]
  have he := Combinatorics.interleaving_counts_end s
  rw [he.1, he.2, historyAt_terminal, historyAt_terminal]
end Rhone.Coalescent
