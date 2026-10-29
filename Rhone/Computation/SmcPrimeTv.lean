/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-! # Exact rational recurrences for the full-ARG and SMC′ total variation bound -/

@[expose] public section
namespace Rhone.Computation.SmcPrimeTv

def hazard (R : Rat) (j : Nat) : Rat := R / ((j : Rat) + 1 + R)

def raceBound (R : Rat) : Nat → Rat
  | 0 => 0
  | j + 1 =>
      let previous := raceBound R j
      previous + hazard R j * (1 - previous)

def harmonic : Nat → Rat
  | 0 => 0
  | j + 1 => harmonic j + 1 / ((j : Rat) + 1)

def doubleBound (R : Rat) : Nat → Rat
  | 0 => 0
  | j + 1 => (1 - hazard R j) * doubleBound R j +
      hazard R j * raceBound R (j + 2)

def quadraticCoefficient : Nat → Rat
  | 0 => 0
  | j + 1 => quadraticCoefficient j + harmonic (j + 2) / ((j : Rat) + 1)

def quadraticBound (R : Rat) (m : Nat) : Rat := R ^ 2 * quadraticCoefficient m

def clippedQuadraticBound (R : Rat) (m : Nat) : Rat := min 1 (quadraticBound R m)

def reportValues (N : Nat) (R : Rat) : Array Rat :=
  let m := N - 1
  #[doubleBound R m, quadraticCoefficient m, quadraticBound R m,
    clippedQuadraticBound R m]

end Rhone.Computation.SmcPrimeTv
