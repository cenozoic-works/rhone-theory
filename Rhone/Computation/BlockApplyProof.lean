/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Init.Data.Range.Lemmas
import Mathlib.Data.List.Range
import Mathlib.Tactic.Ring

/-! # Finite sums in the executable block inverse application -/

@[expose] public section

namespace Rhone.Computation

private theorem push_map_foldl (l : List Nat) (f : Nat → Rat) (out : Array Rat) :
    l.foldl (fun acc t => acc.push (f t)) out = out ++ (l.map f).toArray :=
  List.foldl_push_eq_append

private theorem row_fold_sum (l : List Nat) (f : Nat → Rat) (acc : Rat) :
    l.foldl (fun a u => a + f u) acc = acc + (l.map f).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons u l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

private theorem list_sum_map_range (f : Nat → Rat) (n : Nat) :
    ((List.range n).map f).sum = ∑ u ∈ Finset.range n, f u := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.sum_append, Finset.sum_range_succ, ih]

theorem applyBlockInverse_eq_foldl (p : Params) (i j : Nat) (ps qs : Array Rat)
    (invDet : Rat) (rhs : Array Rat) :
    applyBlockInverse p i j ps qs invDet rhs =
      (List.range (min i j + 1)).foldl (fun out t => out.push
        ((List.range (min i j + 1)).foldl
          (fun acc u => acc + blockInverseEntry p i j ps qs invDet t u * rhs.getD u 0) 0))
        #[] := by
  simp [applyBlockInverse, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

theorem applyBlockInverse_eq_toArray (p : Params) (i j : Nat) (ps qs : Array Rat)
    (invDet : Rat) (rhs : Array Rat) :
    applyBlockInverse p i j ps qs invDet rhs =
      ((List.range (min i j + 1)).map fun t =>
        ∑ u ∈ Finset.range (min i j + 1),
          blockInverseEntry p i j ps qs invDet t u * rhs.getD u 0).toArray := by
  rw [applyBlockInverse_eq_foldl]
  simp_rw [row_fold_sum, zero_add, list_sum_map_range]
  rw [push_map_foldl]
  simp

theorem applyBlockInverse_size (p : Params) (i j : Nat) (ps qs : Array Rat)
    (invDet : Rat) (rhs : Array Rat) :
    (applyBlockInverse p i j ps qs invDet rhs).size = min i j + 1 := by
  simp [applyBlockInverse_eq_toArray]

theorem applyBlockInverse_getD (p : Params) (i j : Nat) (ps qs : Array Rat)
    (invDet : Rat) (rhs : Array Rat) (t : Nat) (ht : t ≤ min i j) :
    (applyBlockInverse p i j ps qs invDet rhs).getD t 0 =
      ∑ u ∈ Finset.range (min i j + 1),
        blockInverseEntry p i j ps qs invDet t u * rhs.getD u 0 := by
  rw [applyBlockInverse_eq_toArray]
  have hlt : t < min i j + 1 := by omega
  simp [hlt]

end Rhone.Computation
