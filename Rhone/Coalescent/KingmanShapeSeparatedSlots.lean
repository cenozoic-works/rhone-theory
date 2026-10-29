/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeSeparatedStep
public import Rhone.Combinatorics.KingmanShapeInterleaving
/-!
# Merger slots of a separated history assigned to its left and right subtrees

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def separatedLeftSlotsRaw {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M)) (a b : ℕ)
    (h : SeparatedForestHistory F H a b) : Finset (Fin (a+b)) :=
  univ.filter (fun k => sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 (k.val+1)) ≠
    sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 k.val))
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem separatedLeftSlotsRaw_card {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : SeparatedForestHistory F H a b) : (separatedLeftSlotsRaw F H a b h).card = a := by
  classical
  let S := separatedLeftSlotsRaw F H a b h
  let count := fun k => (S.filter (fun i => i.val < k)).card
  let r := fun k => (ADR11.roots (sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 k))).card
  have progress (k : ℕ) (hk : k ≤ a+b) : r k + count k = (ADR11.roots F).card := by
    induction k with
    | zero =>
      simp only [count, Nat.not_lt_zero, filter_false, card_empty, Nat.add_zero]
      dsimp only [r]
      rw [Combinatorics.historyAt_zero]
      exact congrArg (fun W => (ADR11.roots W).card) (history_sum_left_projection F H hH)
    | succ k ih =>
      have hi := ih (by omega)
      have ht := separatedForestHistory_step F H hF hH a b h ⟨k, by omega⟩
      dsimp only at ht
      have hc := Combinatorics.finite_slot_count_succ S ⟨k, by omega⟩
      dsimp only at hc
      rcases ht with hleft | hright
      · have hW := sumLeftForest_isForest _ (historyAt_isForest _
          (sumForest_isForest F H hF hH) (a+b) h.1 k)
        have hr := (hW.of_mem_merges hleft.1).2.1
        have hneq : sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 (k+1)) ≠
            sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 k) := by
          intro he
          have hec := congrArg (fun W => (ADR11.roots W).card) he
          omega
        have hm : (⟨k, by omega⟩ : Fin (a+b)) ∈ S :=
          mem_filter.mpr ⟨mem_univ _, hneq⟩
        rw [ite_eq_left hm] at hc
        change count (k+1) = count k + 1 at hc
        change r (k+1) + 1 = r k at hr
        omega
      · have hn : (⟨k, by omega⟩ : Fin (a+b)) ∉ S := by
          intro hm
          exact (mem_filter.mp hm).2 hright.1
        rw [ite_eq_right hn] at hc
        change count (k+1) = count k at hc
        have hr : r (k+1) = r k := congrArg (fun W => (ADR11.roots W).card) hright.1
        omega
  have hc : count (a+b) = S.card := by
    unfold count
    rw [filter_true_of_mem (fun (i : Fin (a+b)) _ => i.isLt)]
  have hp := progress (a+b) le_rfl
  have hr : r (a+b) + a = (ADR11.roots F).card := by
    change (ADR11.roots (sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 (a+b)))).card + a = _
    rw [historyAt_terminal]
    exact h.2.2.1
  change S.card = a
  omega
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def separatedHistorySlots {L M : Type*} [Fintype L] [Fintype M]
    [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : SeparatedForestHistory F H a b) : Combinatorics.HistoryInterleaving a b :=
  ⟨separatedLeftSlotsRaw F H a b h, separatedLeftSlotsRaw_card F H hF hH a b h⟩
end Rhone.Coalescent
