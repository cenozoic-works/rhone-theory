/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Kingman

/-! # Init-only exact comparison of all four canonical moments and array length -/

@[expose] public section
namespace Rhone.Computation.Kingman

def reportValues (n : Nat) : Array Rat :=
  let m := moments n
  #[m.meanTmrca, m.varianceTmrca, m.meanTotalBranchLength, m.varianceTotalBranchLength]

def checkReport (n : Nat) (claim : Array Rat) : Bool :=
  decide (claim = reportValues n)

end Rhone.Computation.Kingman
