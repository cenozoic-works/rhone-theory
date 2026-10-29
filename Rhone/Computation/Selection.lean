/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable one-locus viability selection

Source: crow_kimura1970, sec. 6.2. -/

@[expose] public section
namespace Rhone.Computation.Selection

def sumRange (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumRange f n + f n

def marginalFit (K : Nat) (W : Nat → Nat → Rat) (p : Nat → Rat) (i : Nat) : Rat :=
  sumRange (fun j => W i j * p j) K

def multiMeanFit (K : Nat) (W : Nat → Nat → Rat) (p : Nat → Rat) : Rat :=
  sumRange (fun i => p i * marginalFit K W p i) K

def multiSelStep (K : Nat) (W : Nat → Nat → Rat) (p : Nat → Rat) (i : Nat) : Rat :=
  p i * marginalFit K W p i / multiMeanFit K W p

def meanFit (w11 w12 w22 p : Rat) : Rat :=
  p ^ 2 * w11 + 2 * p * (1 - p) * w12 + (1 - p) ^ 2 * w22

def selStep (w11 w12 w22 p : Rat) : Rat :=
  (p ^ 2 * w11 + p * (1 - p) * w12) / meanFit w11 w12 w22 p

def polyEq (w11 w12 w22 : Rat) : Rat := (w12 - w22) / (2 * w12 - w11 - w22)

def selOrbit (w11 w12 w22 p0 : Rat) : Nat → Rat
  | 0 => p0
  | t + 1 => selStep w11 w12 w22 (selOrbit w11 w12 w22 p0 t)

def interiorEquilibriumExists (w11 w12 w22 : Rat) : Bool :=
  decide ((w11 < w12 ∧ w22 < w12) ∨ (w12 < w11 ∧ w12 < w22))

end Rhone.Computation.Selection
