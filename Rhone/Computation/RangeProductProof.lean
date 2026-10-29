/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
import Init.Data.Range.Lemmas
import Mathlib.Data.List.Range
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-! # Exact products used by the executable block inverse -/

@[expose] public section

namespace Rhone.Computation

theorem rangeProduct_eq_foldl (lo hi : Nat) :
    rangeProduct lo hi = (List.range' (lo + 1) (hi - lo)).foldl (· * ·) 1 := by
  simp [rangeProduct, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem rangeProduct_eq_list_prod (lo hi : Nat) :
    rangeProduct lo hi = (List.range' (lo + 1) (hi - lo)).prod := by
  rw [rangeProduct_eq_foldl, ← List.prod_eq_foldl]

theorem rangeProduct_eq_one_of_le (lo hi : Nat) (h : hi ≤ lo) :
    rangeProduct lo hi = 1 := by
  rw [rangeProduct_eq_list_prod, Nat.sub_eq_zero_of_le h]
  rfl

theorem rangeProduct_zero_eq_factorial (n : Nat) : rangeProduct 0 n = n.factorial := by
  rw [rangeProduct_eq_foldl]
  simp only [Nat.zero_add, Nat.sub_zero, List.range'_eq_map_range, ← List.prod_eq_foldl]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp [Nat.factorial_succ, Nat.mul_comm, Nat.add_comm]

end Rhone.Computation
