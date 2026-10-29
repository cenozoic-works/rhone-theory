/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.HierarchyBlockValueProof
public import Rhone.Computation.HierarchyPrefixProof

/-! # Correctness of one degree scan -/

@[expose] public section

namespace Rhone.Computation

theorem hierarchyStep_preserves_prefix (p : Params) (value : Nat → Nat → Nat → Rat)
    (laws : HierarchyValueLaws p value) (na nb degree row : Nat) (tab : PhiTable)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hrow : row ≤ na) (h : HierarchyPrefix value na nb degree row tab) :
    ∃ next, hierarchyStep p nb degree row tab = .ok next ∧
      HierarchyPrefix value na nb degree (row + 1) next := by
  unfold hierarchyStep
  split
  · rename_i hskip
    exact ⟨tab, rfl, h.next_row_skipped (Or.inl hskip)⟩
  · rename_i hrowdegree
    dsimp only
    split
    · rename_i hskip
      exact ⟨tab, rfl, h.next_row_skipped (Or.inr hskip)⟩
    · rename_i hcol
      have hj : degree - row ≤ nb := by omega
      have hdegree : row + (degree - row) = degree := by omega
      have hlower : ∀ a b d, a ≤ row → b ≤ degree - row →
          a + b < row + (degree - row) → d ≤ min a b →
          tab.get a b d = value a b d := by
        intro a b d ha hb hd ht
        exact h.correct a b d (le_trans ha hrow) (le_trans hb hj) ht
          (Or.inl (by omega))
      have hblock := hierarchyBlock_eq_ok_value p tab value laws row (degree - row)
        hθA hθB hρ hlower
      let block := ((List.range (min row (degree - row) + 1)).map
        (value row (degree - row))).toArray
      refine ⟨{tab with blocks := tab.blocks.set! (row * (nb + 1) + (degree - row)) block},
        ?_, ?_⟩
      · rw [hblock]
        rfl
      · apply h.next_row_updated (degree - row) hrow hj hdegree block
        intro t ht
        have hlt : t < min row (degree - row) + 1 := by omega
        simp [block, hlt]

theorem hierarchyRows_preserve_prefix (p : Params) (value : Nat → Nat → Nat → Rat)
    (laws : HierarchyValueLaws p value) (na nb degree : Nat) (tab : PhiTable)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (h : HierarchyPrefix value na nb degree 0 tab) (n : Nat) (hn : n ≤ na + 1) :
    ∃ next,
      (List.range n).foldlM (fun current row => hierarchyStep p nb degree row current) tab =
        .ok next ∧ HierarchyPrefix value na nb degree n next := by
  induction n with
  | zero => exact ⟨tab, rfl, h⟩
  | succ n ih =>
    obtain ⟨middle, hm, hmiddle⟩ := ih (by omega)
    obtain ⟨next, hs, hnext⟩ := hierarchyStep_preserves_prefix p value laws na nb degree n
      middle hθA hθB hρ (by omega) hmiddle
    refine ⟨next, ?_, hnext⟩
    rw [List.range_succ, List.foldlM_append, hm]
    rw [show (Except.ok middle : Except String PhiTable) = pure middle from rfl]
    simp only [pure_bind, List.foldlM_cons, List.foldlM_nil, bind_pure]
    exact hs

end Rhone.Computation
