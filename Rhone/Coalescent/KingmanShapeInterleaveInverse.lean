/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeSeparatedSlotStep
public import Rhone.Combinatorics.KingmanShapeTraceCompression
public import Rhone.Coalescent.KingmanShapeHistoryInterleaveInjection
/-!
# Reconstruct both subtree histories from a separated chronological history

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem historyInterleave_surjective_separated {L M : Type*}
    [Fintype L] [Fintype M] [DecidableEq L] [DecidableEq M]
    (F : Finset (Finset L)) (H : Finset (Finset M))
    (hF : ADR11.IsForest F) (hH : ADR11.IsForest H) (a b : ℕ)
    (h : SeparatedForestHistory F H a b) :
    ∃ p : (Combinatorics.RankedForestHistory F a × Combinatorics.RankedForestHistory H b) ×
        Combinatorics.HistoryInterleaving a
        b,
      historyInterleave F H hF hH a b p.1.1 p.1.2 p.2 = h.1 := by
  classical
  let s := separatedHistorySlots F H hF hH a b h
  let pL := fun k => sumLeftForest (Combinatorics.historyAt _ (a+b) h.1 k)
  let pR := fun k => sumRightForest (Combinatorics.historyAt _ (a+b) h.1 k)
  have hzL : pL 0 = F := by
    dsimp only [pL]
    rw [Combinatorics.historyAt_zero]
    exact history_sum_left_projection F H hH
  have hzR : pR 0 = H := by
    dsimp only [pR]
    rw [Combinatorics.historyAt_zero]
    exact history_sum_right_projection F H hF
  have stepL (k : Fin (a+b)) : if k ∈ s.1 then pL (k.val+1) ∈ ADR11.merges (pL k.val)
      else pL (k.val+1) = pL k.val := by
    have hs := separatedForestHistory_slot_step F H hF hH a b h k
    by_cases hm : k ∈ s.1
    · rw [ite_eq_left hm] at hs ⊢
      exact hs.1
    · rw [ite_eq_right hm] at hs ⊢
      exact hs.1
  have stepR (k : Fin (a+b)) : if k ∈ s.1ᶜ then pR (k.val+1) ∈ ADR11.merges (pR k.val)
      else pR (k.val+1) = pR k.val := by
    have hs := separatedForestHistory_slot_step F H hF hH a b h k
    by_cases hm : k ∈ s.1
    · rw [ite_eq_left hm] at hs
      rw [ite_eq_right (by simpa only [mem_compl, not_not] using hm)]
      exact hs.2
    · rw [ite_eq_right hm] at hs
      rw [ite_eq_left (mem_compl.mpr hm)]
      exact hs.2
  have hcR : s.1ᶜ.card = b := by
    rw [card_compl, Fintype.card_fin, s.2]
    omega
  have left : ∃ hl : Combinatorics.RankedForestHistory F a, ∀ k ≤ a+b,
      Combinatorics.historyAt F a hl (Combinatorics.interleavingLeft s k) = pL k := by
    exact Eq.mp (congrArg (fun z => ∃ hl : Combinatorics.RankedForestHistory F z, ∀ k ≤ a+b,
      Combinatorics.historyAt F z hl (Combinatorics.interleavingLeft s k) = pL k) s.2)
      (Combinatorics.forestTrace_compress F (a+b) s.1 pL hzL stepL)
  have right : ∃ hr : Combinatorics.RankedForestHistory H b, ∀ k ≤ a+b,
      Combinatorics.historyAt H b hr (Combinatorics.interleavingRight s k) = pR k := by
    exact Eq.mp (congrArg (fun z => ∃ hr : Combinatorics.RankedForestHistory H z, ∀ k ≤ a+b,
      Combinatorics.historyAt H z hr (Combinatorics.interleavingRight s k) = pR k) hcR)
      (Combinatorics.forestTrace_compress H (a+b) s.1ᶜ pR hzR stepR)
  obtain ⟨hl, hleft⟩ := left
  obtain ⟨hr, hright⟩ := right
  refine ⟨((hl, hr), s), Combinatorics.historyAt_history_ext _ (a+b) _ h.1 ?_⟩
  intro k hk
  rw [historyAt_historyInterleave F H hF hH a b hl hr s k hk, hleft k hk, hright k hk]
  exact sumPureForest_decomposition _ (h.2.1 k hk)
end Rhone.Coalescent
