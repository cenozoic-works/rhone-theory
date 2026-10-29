/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
import Init.Data.Range.Lemmas
import Mathlib.Data.List.Range
import Mathlib.Data.List.Basic

/-! # Array invariants for the executable continuant loops -/

@[expose] public section

namespace Rhone.Computation

theorem forwardContinuants_eq_foldl (diag beta : Nat → Rat) (n : Nat) :
    forwardContinuants diag beta n =
      (List.range n).foldl
        (fun ps s => ps.push (diag s * ps.getD (s + 1) 0 - beta s * ps.getD s 0))
        #[0, 1] := by
  simp [forwardContinuants, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

theorem forwardContinuants_zero (diag beta : Nat → Rat) :
    forwardContinuants diag beta 0 = #[0, 1] := by
  rw [forwardContinuants_eq_foldl]
  rfl

theorem forwardContinuants_succ (diag beta : Nat → Rat) (n : Nat) :
    forwardContinuants diag beta (n + 1) =
      (forwardContinuants diag beta n).push
        (diag n * (forwardContinuants diag beta n).getD (n + 1) 0 -
          beta n * (forwardContinuants diag beta n).getD n 0) := by
  rw [forwardContinuants_eq_foldl, forwardContinuants_eq_foldl, List.range_succ,
    List.foldl_append]
  rfl

theorem forwardContinuants_size (diag beta : Nat → Rat) (n : Nat) :
    (forwardContinuants diag beta n).size = n + 2 := by
  induction n with
  | zero => simp [forwardContinuants_zero]
  | succ n ih =>
    rw [forwardContinuants_succ, Array.size_push, ih]

private theorem getD_push_lt (xs : Array Rat) (v : Rat) (k : Nat) (h : k < xs.size) :
    (xs.push v).getD k 0 = xs.getD k 0 := by
  simp [Array.getElem?_push, Nat.ne_of_lt h]

private theorem getD_push_size (xs : Array Rat) (v : Rat) :
    (xs.push v).getD xs.size 0 = v := by
  simp

theorem forwardContinuants_getD_zero (diag beta : Nat → Rat) (n : Nat) :
    (forwardContinuants diag beta n).getD 0 0 = 0 := by
  induction n with
  | zero => simp [forwardContinuants_zero]
  | succ n ih =>
    rw [forwardContinuants_succ, getD_push_lt, ih]
    rw [forwardContinuants_size]
    omega

theorem forwardContinuants_getD (diag beta value : Nat → Rat)
    (hzero : value 0 = 1)
    (n r : Nat)
    (hstep : ∀ s, s < n → value (s + 1) = diag s * value s -
      beta s * (if s = 0 then 0 else value (s - 1)))
    (hr : r ≤ n) :
    (forwardContinuants diag beta n).getD (r + 1) 0 = value r := by
  induction n generalizing r with
  | zero =>
    have : r = 0 := by omega
    subst r
    simp [forwardContinuants_zero, hzero]
  | succ n ih =>
    have hstep' : ∀ s, s < n → value (s + 1) = diag s * value s -
        beta s * (if s = 0 then 0 else value (s - 1)) :=
      fun s hs => hstep s (by omega)
    by_cases h : r ≤ n
    · rw [forwardContinuants_succ, getD_push_lt, ih r hstep' h]
      rw [forwardContinuants_size]
      omega
    · have he : r = n + 1 := by omega
      subst r
      rw [forwardContinuants_succ]
      have hs : n + 1 + 1 = (forwardContinuants diag beta n).size := by
        rw [forwardContinuants_size]
      rw [hs, getD_push_size, ih n hstep' le_rfl, hstep n (by omega)]
      by_cases hn : n = 0
      · subst n
        simp [forwardContinuants_zero]
      · have hprev : n = n - 1 + 1 := by omega
        have hp : (forwardContinuants diag beta n).getD n 0 = value (n - 1) := by
          conv_lhs => arg 2; rw [hprev]
          exact ih (n - 1) hstep' (by omega)
        rw [hp]
        simp [hn]

end Rhone.Computation
