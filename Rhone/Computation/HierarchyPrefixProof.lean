/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.HierarchyIndexProof

/-! # Degree and row prefixes of the finite hierarchy -/

@[expose] public section

namespace Rhone.Computation

structure HierarchyPrefix (value : Nat → Nat → Nat → Rat)
    (na nb degree row : Nat) (tab : PhiTable) : Prop where
  width : tab.nb = nb
  allocated : tab.blocks.size = (na + 1) * (nb + 1)
  correct : ∀ a b t, a ≤ na → b ≤ nb → t ≤ min a b →
    (a + b < degree ∨ (a + b = degree ∧ a < row)) → tab.get a b t = value a b t

theorem hierarchyPrefix_initial (value : Nat → Nat → Nat → Rat) (na nb : Nat) :
    HierarchyPrefix value na nb 0 0
      ⟨nb, Array.replicate ((na + 1) * (nb + 1)) #[]⟩ := by
  refine ⟨rfl, by simp, ?_⟩
  intro a b t ha hb ht hp
  omega

theorem HierarchyPrefix.next_degree {value : Nat → Nat → Nat → Rat}
    {na nb degree : Nat} {tab : PhiTable}
    (h : HierarchyPrefix value na nb degree (na + 1) tab) :
    HierarchyPrefix value na nb (degree + 1) 0 tab := by
  refine ⟨h.width, h.allocated, ?_⟩
  intro a b t ha hb ht hp
  apply h.correct a b t ha hb ht
  omega

theorem HierarchyPrefix.complete {value : Nat → Nat → Nat → Rat}
    {na nb : Nat} {tab : PhiTable}
    (h : HierarchyPrefix value na nb (na + nb + 1) 0 tab)
    (a b t : Nat) (ha : a ≤ na) (hb : b ≤ nb) (ht : t ≤ min a b) :
    tab.get a b t = value a b t := by
  exact h.correct a b t ha hb ht (Or.inl (by omega))

theorem HierarchyPrefix.preserve_read {value : Nat → Nat → Nat → Rat}
    {na nb degree row : Nat} {tab : PhiTable}
    (h : HierarchyPrefix value na nb degree row tab) (j : Nat)
    (hj : j ≤ nb) (hdegree : row + j = degree) (block : Array Rat)
    (a b t : Nat) (ha : a ≤ na) (hb : b ≤ nb) (ht : t ≤ min a b)
    (hp : a + b < degree ∨ (a + b = degree ∧ a < row)) :
    ({tab with blocks := tab.blocks.set! (row * (nb + 1) + j) block} : PhiTable).get
      a b t = value a b t := by
  have hne : row * (tab.nb + 1) + j ≠ a * (tab.nb + 1) + b := by
    rw [h.width]
    intro heq
    obtain ⟨hr, hj'⟩ := hierarchyIndex_injective nb row j a b hj hb heq
    omega
  have hw : row * (nb + 1) + j = row * (tab.nb + 1) + j := by rw [h.width]
  rw [hw, PhiTable.get_setBlock_other tab row j a b t block hne]
  exact h.correct a b t ha hb ht hp

theorem HierarchyPrefix.next_row_skipped {value : Nat → Nat → Nat → Rat}
    {na nb degree row : Nat} {tab : PhiTable}
    (h : HierarchyPrefix value na nb degree row tab)
    (hskip : row > degree ∨ degree - row > nb) :
    HierarchyPrefix value na nb degree (row + 1) tab := by
  refine ⟨h.width, h.allocated, ?_⟩
  intro a b t ha hb ht hp
  apply h.correct a b t ha hb ht
  omega

theorem HierarchyPrefix.next_row_updated {value : Nat → Nat → Nat → Rat}
    {na nb degree row : Nat} {tab : PhiTable}
    (h : HierarchyPrefix value na nb degree row tab) (j : Nat)
    (hrow : row ≤ na) (hj : j ≤ nb) (hdegree : row + j = degree)
    (block : Array Rat) (hblock : ∀ t, t ≤ min row j → block.getD t 0 = value row j t) :
    HierarchyPrefix value na nb degree (row + 1)
      {tab with blocks := tab.blocks.set! (row * (nb + 1) + j) block} := by
  refine ⟨h.width, ?_, ?_⟩
  · simpa only [Array.size_set!] using h.allocated
  · intro a b t ha hb ht hp
    by_cases hab : a = row ∧ b = j
    · obtain ⟨haeq, hbeq⟩ := hab
      subst a
      subst b
      have hindex : row * (tab.nb + 1) + j < tab.blocks.size := by
        rw [h.width, h.allocated]
        exact hierarchyIndex_lt na nb row j hrow hj
      have hw : row * (nb + 1) + j = row * (tab.nb + 1) + j := by rw [h.width]
      rw [hw, PhiTable.get_setBlock_self tab row j t block hindex ht]
      exact hblock t ht
    · have hp' : a + b < degree ∨ (a + b = degree ∧ a < row) := by omega
      exact h.preserve_read j hj hdegree block a b t ha hb ht hp'

end Rhone.Computation
