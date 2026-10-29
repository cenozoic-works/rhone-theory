/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-! # Executable infinite-sites formula values -/

@[expose] public section
namespace Rhone.Computation.Sfs

def harmonic : Nat → Rat
  | 0 => 0
  | n + 1 => harmonic n + 1 / ((n + 1 : Nat) : Rat)

def harmonic2 : Nat → Rat
  | 0 => 0
  | n + 1 => harmonic2 n + 1 / (((n + 1 : Nat) : Rat) ^ 2)

structure Coefficients where
  a1 : Rat
  a2 : Rat
  b1 : Rat
  b2 : Rat
  c1 : Rat
  c2 : Rat
  e1 : Rat
  e2 : Rat

def coefficients (n : Nat) : Coefficients :=
  let nr : Rat := n
  let a1 := harmonic (n - 1)
  let a2 := harmonic2 (n - 1)
  let b1 := (nr + 1) / (3 * (nr - 1))
  let b2 := 2 * (nr ^ 2 + nr + 3) / (9 * nr * (nr - 1))
  let c1 := b1 - 1 / a1
  let c2 := b2 - (nr + 2) / (a1 * nr) + a2 / a1 ^ 2
  ⟨a1, a2, b1, b2, c1, c2, c1 / a1, c2 / (a1 ^ 2 + a2)⟩

def meanBin (theta : Rat) (i : Nat) : Rat := theta / (i : Rat)

def spectrum (n : Nat) (theta : Rat) : Array Rat :=
  ((List.range (n - 1)).map (fun offset => meanBin theta (offset + 1))).toArray

structure Moments where
  meanSegregating : Rat
  varianceSegregating : Rat
  meanPairwise : Rat
  secondMomentPairwise : Rat
  variancePairwise : Rat

def moments (n : Nat) (theta : Rat) : Moments :=
  let c := coefficients n
  ⟨theta * c.a1, theta * c.a1 + theta ^ 2 * c.a2, theta,
    c.b1 * theta + (1 + c.b2) * theta ^ 2,
    c.b1 * theta + c.b2 * theta ^ 2⟩

def watterson (n : Nat) (segregating : Rat) : Rat :=
  segregating / (coefficients n).a1

end Rhone.Computation.Sfs
