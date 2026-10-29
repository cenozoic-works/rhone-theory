/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsCheck

/-! # Soundness and completeness of the typed formula-array comparison -/

@[expose] public section
namespace Rhone.Computation.Sfs

theorem checkReport_iff (n : Nat) (theta : Rat) (claim : Array Rat) :
    checkReport n theta claim = true ↔ claim = reportValues n theta := by
  simp [checkReport]

theorem checkReport_complete (n : Nat) (theta : Rat) :
    checkReport n theta (reportValues n theta) = true := by
  simp [checkReport]

end Rhone.Computation.Sfs
