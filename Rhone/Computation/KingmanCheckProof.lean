/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.KingmanCheck

/-! # Exact typed four-value acceptance -/

@[expose] public section
namespace Rhone.Computation.Kingman

theorem checkReport_iff (n : Nat) (claim : Array Rat) :
    checkReport n claim = true ↔ claim = reportValues n := by
  simp [checkReport]

theorem checkReport_complete (n : Nat) :
    checkReport n (reportValues n) = true := by
  simp [checkReport]

end Rhone.Computation.Kingman
