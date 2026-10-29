/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.RangeProductProof
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Products along a tridiagonal block -/

@[expose] public section

namespace Rhone.Computation

private theorem list_prod_map_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).prod = ∏ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.range_succ, List.prod_append, Finset.prod_range_succ, ih]

theorem rangeProduct_eq_prod_Ico (lo hi : Nat) :
    rangeProduct lo hi = ∏ k ∈ Finset.Ico (lo + 1) (hi + 1), k := by
  rw [rangeProduct_eq_list_prod, List.range'_eq_map_range, list_prod_map_range,
    Finset.prod_Ico_eq_prod_range]
  simp

theorem rangeProduct_eq_prod_succ (lo hi : Nat) :
    rangeProduct lo hi = ∏ k ∈ Finset.Ico lo hi, (k + 1) := by
  rw [rangeProduct_eq_prod_Ico]
  exact (Finset.prod_Ico_add' (fun x : Nat => x) lo hi 1).symm

theorem rangeProduct_sub_eq_prod (i t u : Nat) (htu : t ≤ u) (hui : u ≤ i) :
    rangeProduct (i - u) (i - t) = ∏ s ∈ Finset.Ico t u, (i - s) := by
  rw [rangeProduct_eq_prod_Ico]
  have hu : i + 1 - u = i - u + 1 := by omega
  have ht : i + 1 - t = i - t + 1 := by omega
  simpa only [hu, ht] using
    (Finset.prod_Ico_reflect (fun x : Nat => x) t (m := u) (n := i) (by omega)).symm

end Rhone.Computation
