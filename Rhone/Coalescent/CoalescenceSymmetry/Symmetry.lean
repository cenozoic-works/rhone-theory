/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ArgLumping.Tags

/-! # Symmetry of the count-only coalescence successor -/

@[expose] public section

namespace Rhone.Coalescent.CoalescenceSymmetry

open ArgLumping

theorem mergeTag_comm (i j : Tag) : mergeTag i j = mergeTag j i := by
  cases i <;> cases j <;> rfl

theorem coalCombo_comm (C : Tag × Tag → ℕ) (i j : Tag × Tag) :
    coalCombo C i j = coalCombo C j i := by
  have hA : (i.1 ≠ Tag.N ∧ j.1 ≠ Tag.N ∧ totA C = 2) ↔
      (j.1 ≠ Tag.N ∧ i.1 ≠ Tag.N ∧ totA C = 2) := and_left_comm
  have hB : (i.2 ≠ Tag.N ∧ j.2 ≠ Tag.N ∧ totB C = 2) ↔
      (j.2 ≠ Tag.N ∧ i.2 ≠ Tag.N ∧ totB C = 2) := and_left_comm
  simp only [coalCombo, hA, hB, mergeTag_comm i.1 j.1, mergeTag_comm i.2 j.2]

theorem coalC_comm (C : Tag × Tag → ℕ) (i j : Tag × Tag) :
    coalC C i j = coalC C j i := by
  funext c
  simp only [coalC, coalCombo_comm C i j]
  exact Nat.sub_right_comm _ _ _

end Rhone.Coalescent.CoalescenceSymmetry
