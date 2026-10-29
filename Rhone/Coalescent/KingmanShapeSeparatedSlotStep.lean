/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeSeparatedSlots
/-!
# The recovered slot set classifies every subtree merger step

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem separatedForestHistory_slot_step {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : SeparatedForestHistory F H a b) (k : Fin (a + b)) :
    if k ∈ (separatedHistorySlots F H hF hH a b h).1 then
      sumLeftForest (Combinatorics.historyAt _ (a + b) h.1 (k.val+1)) ∈
        ADR11.merges (sumLeftForest (Combinatorics.historyAt _ (a + b) h.1 k.val)) ∧
      sumRightForest (Combinatorics.historyAt _ (a + b) h.1 (k.val+1)) =
        sumRightForest (Combinatorics.historyAt _ (a + b) h.1 k.val)
    else
      sumLeftForest (Combinatorics.historyAt _ (a + b) h.1 (k.val+1)) =
        sumLeftForest (Combinatorics.historyAt _ (a + b) h.1 k.val) ∧
      sumRightForest (Combinatorics.historyAt _ (a + b) h.1 (k.val+1)) ∈
        ADR11.merges (sumRightForest (Combinatorics.historyAt _ (a + b) h.1 k.val)) := by
  classical
  let s := separatedHistorySlots F H hF hH a b h
  have ht := separatedForestHistory_step F H hF hH a b h k
  have hmem : k ∈ s.1 ↔ sumLeftForest (Combinatorics.historyAt _ (a + b) h.1 (k.val+1)) ≠
      sumLeftForest (Combinatorics.historyAt _ (a + b) h.1 k.val) := by
    simp only [s, separatedHistorySlots, separatedLeftSlotsRaw, mem_filter, mem_univ, true_and]
  by_cases hm : k ∈ s.1
  · rw [ite_eq_left hm]
    rcases ht with hl | hr
    · exact hl
    · exact False.elim ((hmem.mp hm) hr.1)
  · rw [ite_eq_right hm]
    rcases ht with hl | hr
    · have hw := sumLeftForest_isForest _ (historyAt_isForest _
        (sumForest_isForest F H hF hH) _ h.1 k.val)
      have hc := (hw.of_mem_merges hl.1).2.1
      have he : sumLeftForest (Combinatorics.historyAt _ (a + b) h.1 (k.val+1)) =
          sumLeftForest (Combinatorics.historyAt _ (a + b) h.1 k.val) := not_not.mp
              (fun hn => hm (hmem.mpr hn))
      have hec := congrArg (fun W => (ADR11.roots W).card) he
      omega
    · exact hr
end Rhone.Coalescent
