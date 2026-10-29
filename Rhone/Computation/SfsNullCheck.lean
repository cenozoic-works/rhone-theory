/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsNull

/-! # Typed exact Watterson uncertainty comparison -/

@[expose] public section
namespace Rhone.Computation.SfsNull

def reportValues (n : Nat) (theta : Rat) (observed : Option Nat) : Array Rat :=
  let c := Sfs.coefficients n
  let m := moments n theta
  let base := #[c.a1, c.a2, m.meanSegregating, m.varianceSegregating,
    m.meanWatterson, m.varianceWatterson]
  match observed with
  | none => base
  | some count => base ++ #[Sfs.watterson n (count : Rat),
      observedWattersonVariance n (count : Rat)]

def checkReport (n : Nat) (theta : Rat) (observed : Option Nat) (claim : Array Rat) : Bool :=
  decide (2 ≤ n ∧ 0 ≤ theta ∧ claim = reportValues n theta observed)

end Rhone.Computation.SfsNull
