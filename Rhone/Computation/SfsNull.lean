/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Sfs

/-! # Exact total-S and Watterson moments, reusing existing Init-only Sfs coefficients -/

@[expose] public section
namespace Rhone.Computation.SfsNull

structure Moments where
  meanSegregating : Rat
  varianceSegregating : Rat
  meanWatterson : Rat
  varianceWatterson : Rat

def moments (n : Nat) (theta : Rat) : Moments :=
  let old := Sfs.moments n theta
  let c := Sfs.coefficients n
  ⟨old.meanSegregating, old.varianceSegregating, theta,
    theta / c.a1 + theta ^ 2 * c.a2 / c.a1 ^ 2⟩

def observedWattersonVariance (n : Nat) (segregating : Rat) : Rat :=
  let c := Sfs.coefficients n
  (c.a1 ^ 2 * segregating + c.a2 * segregating ^ 2) /
    (c.a1 ^ 2 * (c.a1 ^ 2 + c.a2))

end Rhone.Computation.SfsNull
