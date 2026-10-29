/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.BlockSuccessProof
public import Rhone.Computation.ParamsProof
import Init.Data.Range.Lemmas
import Mathlib.Data.List.Range

/-! # Total success of the hierarchy and ordered sampling implementation -/

@[expose] public section

namespace Rhone.Computation

private theorem foldlM_total {α β : Type} (l : List α) (f : β → α → Except String β)
    (h : ∀ b a, ∃ value, f b a = .ok value) (initial : β) :
    ∃ value, l.foldlM f initial = .ok value := by
  induction l generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons a l ih =>
    obtain ⟨next, hn⟩ := h initial a
    obtain ⟨value, hv⟩ := ih next
    exact ⟨value, by rw [List.foldlM_cons, hn]; exact hv⟩

theorem hierarchyBlock_success (p : Params) (tab : PhiTable) (i j : Nat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho) :
    ∃ block, hierarchyBlock p tab i j = .ok block := by
  unfold hierarchyBlock
  split
  · exact ⟨_, rfl⟩
  · rename_i h00
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · have hij : 0 < i + j := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq] at h00
          omega
        exact ⟨_, solveBlock_eq_ok p i j _ hθA hθB hρ hij⟩

theorem hierarchyStep_success (p : Params) (nb degree i : Nat) (tab : PhiTable)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho) :
    ∃ next, hierarchyStep p nb degree i tab = .ok next := by
  unfold hierarchyStep
  split
  · exact ⟨tab, rfl⟩
  · dsimp only
    split
    · exact ⟨tab, rfl⟩
    · obtain ⟨block, hb⟩ := hierarchyBlock_success p tab i (degree - i) hθA hθB hρ
      exact ⟨_, by rw [hb]; rfl⟩

theorem phiTable_eq_foldlM (p : Params) (na nb : Nat) :
    phiTable p na nb =
      (List.range (na + nb + 1)).foldlM (fun tab degree =>
        (List.range (na + 1)).foldlM (fun tab i => hierarchyStep p nb degree i tab) tab)
        ⟨nb, Array.replicate ((na + 1) * (nb + 1)) #[]⟩ := by
  simp [phiTable, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

theorem phiTable_success (p : Params) (na nb : Nat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho) :
    ∃ tab, phiTable p na nb = .ok tab := by
  rw [phiTable_eq_foldlM]
  apply foldlM_total
  intro tab degree
  apply foldlM_total
  intro tab i
  exact hierarchyStep_success p nb degree i tab hθA hθB hρ

theorem q_success (p : Params) (c : Config) (hp : p.valid = true)
    (ha : c.a.size = 2) (hb : c.b.size = 2) (hc : c.c.size = 4) :
    ∃ value, q p c = .ok value := by
  obtain ⟨hθA, hθB, hρ, _⟩ := (Params.valid_iff p).mp hp
  obtain ⟨tab, ht⟩ := phiTable_success p c.block.1 c.block.2 hθA hθB hρ
  exact ⟨assemble tab (polynomial p c), by simp [q, hp, ha, hb, hc, ht]⟩

end Rhone.Computation
