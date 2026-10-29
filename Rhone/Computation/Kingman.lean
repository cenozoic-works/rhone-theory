/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Sfs

/-! # Exact canonical pair-rate-one genealogy moments -/

@[expose] public section
namespace Rhone.Computation.Kingman

def holding (k : Nat) : Rat := 2 / ((k : Rat) * ((k : Rat) - 1))

def varianceTime : Nat → Rat
  | 0 => 0
  | n + 1 => varianceTime n + holding (n + 1) ^ 2

structure Moments where
  meanTmrca : Rat
  varianceTmrca : Rat
  meanTotalBranchLength : Rat
  varianceTotalBranchLength : Rat

def moments (n : Nat) : Moments :=
  let c := Sfs.coefficients n
  ⟨if n = 0 then 0 else 2 * (1 - 1 / (n : Rat)), varianceTime n,
    2 * c.a1, 4 * c.a2⟩

end Rhone.Computation.Kingman
