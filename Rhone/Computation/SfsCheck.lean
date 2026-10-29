/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Sfs

/-! # Exact comparison of the nine formula scalars and all unfolded mean bins -/

@[expose] public section
namespace Rhone.Computation.Sfs

def reportValues (n : Nat) (theta : Rat) : Array Rat :=
  let c := coefficients n
  let m := moments n theta
  #[c.a1, c.a2, c.b1, c.b2, m.meanSegregating, m.varianceSegregating,
    m.meanPairwise, m.secondMomentPairwise, m.variancePairwise] ++ spectrum n theta

def checkReport (n : Nat) (theta : Rat) (claim : Array Rat) : Bool :=
  decide (claim = reportValues n theta)

end Rhone.Computation.Sfs
