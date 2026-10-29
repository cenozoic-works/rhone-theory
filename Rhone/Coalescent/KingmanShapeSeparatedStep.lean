/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeSeparatedInsert
/-! # Each merger of a separated history changes exactly one subtree forest -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem sumPureForest_merge_step {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M] (W W' : Finset (Finset (L ⊕ M)))
    (hW : ADR11.IsForest W) (hm : W' ∈ ADR11.merges W) (hpure : SumPureForest W') :
    (sumLeftForest W' ∈ ADR11.merges (sumLeftForest W) ∧
      sumRightForest W' = sumRightForest W) ∨
    (sumLeftForest W' = sumLeftForest W ∧
      sumRightForest W' ∈ ADR11.merges (sumRightForest W)) := by
  obtain ⟨B, hBr, C, hCr, hBC, rfl⟩ := ADR11.mem_merges.mp hm
  rcases hpure (B ∪ C) (mem_insert_self _ _) with hL | hR
  · obtain ⟨D, hDr, hDB⟩ := sumLeftForest_root W B hBr (subset_union_left.trans hL)
    obtain ⟨E, hEr, hEC⟩ := sumLeftForest_root W C hCr (subset_union_right.trans hL)
    have hDE : D ≠ E := by
      intro he
      apply hBC
      rw [← hDB, ← hEC, he]
    have hnew : B ∪ C = (D ∪ E).map Function.Embedding.inl := by
      rw [map_union, hDB, hEC]
    have hne : (D ∪ E).Nonempty :=
      ((sumLeftForest_isForest W hW).1 D (ADR11.roots_subset _ hDr)).mono subset_union_left
    apply Or.inl
    constructor
    · rw [hnew, sumLeftForest_insert_left]
      exact ADR11.mem_merges.mpr ⟨D, hDr, E, hEr, hDE, rfl⟩
    · rw [hnew, sumRightForest_insert_left W _ hne]
  · obtain ⟨D, hDr, hDB⟩ := sumRightForest_root W B hBr (subset_union_left.trans hR)
    obtain ⟨E, hEr, hEC⟩ := sumRightForest_root W C hCr (subset_union_right.trans hR)
    have hDE : D ≠ E := by
      intro he
      apply hBC
      rw [← hDB, ← hEC, he]
    have hnew : B ∪ C = (D ∪ E).map Function.Embedding.inr := by
      rw [map_union, hDB, hEC]
    have hne : (D ∪ E).Nonempty :=
      ((sumRightForest_isForest W hW).1 D (ADR11.roots_subset _ hDr)).mono subset_union_left
    apply Or.inr
    constructor
    · rw [hnew, sumLeftForest_insert_right W _ hne]
    · rw [hnew, sumRightForest_insert_right]
      exact ADR11.mem_merges.mpr ⟨D, hDr, E, hEr, hDE, rfl⟩
theorem separatedForestHistory_step {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : SeparatedForestHistory F H a b) (k : Fin (a + b)) :
    (sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 (k.val+1)) ∈
        ADR11.merges (sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 k.val)) ∧
      sumRightForest (Combinatorics.historyAt _ (a+b) h.1 (k.val+1)) =
        sumRightForest (Combinatorics.historyAt _ (a+b) h.1 k.val)) ∨
    (sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 (k.val+1)) =
        sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 k.val) ∧
      sumRightForest (Combinatorics.historyAt _ (a+b) h.1 (k.val+1)) ∈
        ADR11.merges (sumRightForest (Combinatorics.historyAt _ (a+b) h.1 k.val))) := by
  have hzero := sumForest_isForest F H hF hH
  exact sumPureForest_merge_step _ _ (historyAt_isForest _ hzero _ h.1 k.val)
    (Combinatorics.historyAt_next_merge _ _ h.1 k.val k.isLt) (h.2.1 (k.val+1) k.isLt)
end Rhone.Coalescent
