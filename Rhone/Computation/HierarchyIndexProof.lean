/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
import Mathlib.Data.Nat.Basic

/-! # Rectangle indices and hierarchy updates -/

@[expose] public section

namespace Rhone.Computation

theorem hierarchyIndex_lt (na nb i j : Nat) (hi : i ≤ na) (hj : j ≤ nb) :
    i * (nb + 1) + j < (na + 1) * (nb + 1) := by
  calc
    i * (nb + 1) + j < i * (nb + 1) + (nb + 1) :=
      Nat.add_lt_add_left (by omega) _
    _ = (i + 1) * (nb + 1) := by simp [Nat.add_mul]
    _ ≤ (na + 1) * (nb + 1) := Nat.mul_le_mul_right _ (by omega)

theorem hierarchyIndex_injective (nb i j i' j' : Nat) (hj : j ≤ nb) (hj' : j' ≤ nb)
    (h : i * (nb + 1) + j = i' * (nb + 1) + j') : i = i' ∧ j = j' := by
  have hd := congrArg (fun index => index / (nb + 1)) h
  have hi : i = i' := by
    simpa only [Nat.mul_comm i (nb + 1), Nat.mul_comm i' (nb + 1),
      Nat.mul_add_div (Nat.succ_pos nb), Nat.div_eq_of_lt (by omega : j < nb + 1),
      Nat.div_eq_of_lt (by omega : j' < nb + 1), Nat.add_zero] using hd
  refine ⟨hi, ?_⟩
  subst i'
  omega

theorem PhiTable.get_setBlock_self (tab : PhiTable) (i j t : Nat) (block : Array Rat)
    (hi : i * (tab.nb + 1) + j < tab.blocks.size) (ht : t ≤ min i j) :
    ({tab with blocks := tab.blocks.set! (i * (tab.nb + 1) + j) block} : PhiTable).get
      i j t = block.getD t 0 := by
  have hget : (tab.blocks.set! (i * (tab.nb + 1) + j) block).getD
      (i * (tab.nb + 1) + j) #[] = block := by
    exact Array.getElem!_set!_self tab.blocks _ block hi
  simp only [PhiTable.get, Nat.not_lt_of_ge ht, ite_false, hget]

theorem PhiTable.get_setBlock_other (tab : PhiTable) (i j a b t : Nat) (block : Array Rat)
    (hne : i * (tab.nb + 1) + j ≠ a * (tab.nb + 1) + b) :
    ({tab with blocks := tab.blocks.set! (i * (tab.nb + 1) + j) block} : PhiTable).get
      a b t = tab.get a b t := by
  have hget : (tab.blocks.set! (i * (tab.nb + 1) + j) block).getD
      (a * (tab.nb + 1) + b) #[] = tab.blocks.getD (a * (tab.nb + 1) + b) #[] := by
    exact Array.getElem!_set!_ne tab.blocks _ _ block hne
  simp only [PhiTable.get, hget]

end Rhone.Computation
