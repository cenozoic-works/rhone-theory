/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SmcPrimeTv

/-! # Exact acceptance at the typed four-rational boundary -/

@[expose] public section
namespace Rhone.Computation.SmcPrimeTv

def checkReport (N : Nat) (R : Rat) (claim : Array Rat) : Bool :=
  decide (1 ≤ N ∧ 0 ≤ R ∧ claim = reportValues N R)

theorem checkReport_iff (N : Nat) (R : Rat) (claim : Array Rat) :
    checkReport N R claim = true ↔ 1 ≤ N ∧ 0 ≤ R ∧ claim = reportValues N R := by
  simp [checkReport]

theorem checkReport_complete (N : Nat) (hN : 1 ≤ N) (R : Rat) (hR : 0 ≤ R) :
    checkReport N R (reportValues N R) = true := by
  simp [checkReport, hN, hR]

end Rhone.Computation.SmcPrimeTv
