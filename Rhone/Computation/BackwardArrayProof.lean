/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Hierarchy
import Init.Data.Range.Lemmas
import Mathlib.Data.List.Range
import Mathlib.Data.List.Basic

/-! # Finite iterations of the executable backward continuant loop -/

@[expose] public section

namespace Rhone.Computation

private def backwardPrefix (diag beta : Nat → Rat) (m steps : Nat) : Array Rat :=
  (List.range steps).foldl (fun qs k =>
    let s := m - k
    qs.set! s (diag s * qs.getD (s + 1) 0 - beta (s + 1) * qs.getD (s + 2) 0))
    ((Array.replicate (m + 3) 0).set! (m + 1) 1)

private theorem backwardPrefix_succ (diag beta : Nat → Rat) (m k : Nat) :
    backwardPrefix diag beta m (k + 1) =
      (backwardPrefix diag beta m k).set! (m - k)
        (diag (m - k) * (backwardPrefix diag beta m k).getD (m - k + 1) 0 -
          beta (m - k + 1) * (backwardPrefix diag beta m k).getD (m - k + 2) 0) := by
  simp only [backwardPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

private theorem backwardPrefix_size (diag beta : Nat → Rat) (m k : Nat) :
    (backwardPrefix diag beta m k).size = m + 3 := by
  induction k with
  | zero => simp [backwardPrefix]
  | succ k ih => simp [backwardPrefix_succ, ih]

private theorem getD_set_self (xs : Array Rat) (i : Nat) (v : Rat) (h : i < xs.size) :
    (xs.set! i v).getD i 0 = v := by
  simp [h]

private theorem getD_set_ne (xs : Array Rat) (i j : Nat) (v : Rat) (h : i ≠ j) :
    (xs.set! i v).getD j 0 = xs.getD j 0 := by
  simp [h]

private theorem backwardPrefix_getD (diag beta value : Nat → Rat) (m k r : Nat)
    (hend : value (m + 1) = 1) (hnext : value (m + 2) = 0)
    (hstep : ∀ s, s ≤ m → value s =
      diag s * value (s + 1) - beta (s + 1) * value (s + 2))
    (hk : k ≤ m + 1) (hr : m + 1 - k ≤ r) (hrtop : r ≤ m + 2) :
    (backwardPrefix diag beta m k).getD r 0 = value r := by
  induction k generalizing r with
  | zero =>
    have h1 : m + 1 < m + 3 := by omega
    have h2 : m + 2 < m + 3 := by omega
    have he : r = m + 1 ∨ r = m + 2 := by omega
    rcases he with rfl | rfl
    · simp [backwardPrefix, hend, h1]
    · simp [backwardPrefix, hnext, h2]
  | succ k ih =>
    have hk' : k ≤ m + 1 := by omega
    have hs : m - k < (backwardPrefix diag beta m k).size := by
      rw [backwardPrefix_size]
      omega
    have htail : m + 1 - k = m - k + 1 := by omega
    by_cases he : r = m - k
    · subst r
      rw [backwardPrefix_succ, getD_set_self _ _ _ hs,
        ih (m - k + 1) hk' (by omega) (by omega),
        ih (m - k + 2) hk' (by omega) (by omega)]
      exact (hstep (m - k) (Nat.sub_le _ _)).symm
    · rw [backwardPrefix_succ, getD_set_ne _ _ _ _ (Ne.symm he)]
      exact ih r hk' (by omega) hrtop

theorem backwardContinuants_eq_foldl (diag beta : Nat → Rat) (m : Nat) :
    backwardContinuants diag beta m =
      (List.range (m + 1)).foldl (fun qs k =>
        let s := m - k
        qs.set! s (diag s * qs.getD (s + 1) 0 - beta (s + 1) * qs.getD (s + 2) 0))
        ((Array.replicate (m + 3) 0).set! (m + 1) 1) := by
  simp [backwardContinuants, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

theorem backwardContinuants_size (diag beta : Nat → Rat) (m : Nat) :
    (backwardContinuants diag beta m).size = m + 3 := by
  rw [backwardContinuants_eq_foldl]
  exact backwardPrefix_size diag beta m (m + 1)

theorem backwardContinuants_getD (diag beta value : Nat → Rat) (m r : Nat)
    (hend : value (m + 1) = 1) (hnext : value (m + 2) = 0)
    (hstep : ∀ s, s ≤ m → value s =
      diag s * value (s + 1) - beta (s + 1) * value (s + 2))
    (hr : r ≤ m + 2) :
    (backwardContinuants diag beta m).getD r 0 = value r := by
  rw [backwardContinuants_eq_foldl]
  exact backwardPrefix_getD diag beta value m (m + 1) r hend hnext hstep
    le_rfl (by omega) hr

end Rhone.Computation
