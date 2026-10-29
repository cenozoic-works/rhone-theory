/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsNullCheck

/-! # Soundness and completeness at the typed rational-array boundary -/

@[expose] public section
namespace Rhone.Computation.SfsNull

theorem checkReport_iff (n : Nat) (theta : Rat) (observed : Option Nat) (claim : Array Rat) :
    checkReport n theta observed claim = true ↔
      2 ≤ n ∧ 0 ≤ theta ∧ claim = reportValues n theta observed := by
  simp [checkReport]

theorem checkReport_complete {n : Nat} (hn : 2 ≤ n) (theta : Rat) (htheta : 0 ≤ theta)
    (observed : Option Nat) :
    checkReport n theta observed (reportValues n theta observed) = true := by
  simp [checkReport, hn, htheta]

end Rhone.Computation.SfsNull
