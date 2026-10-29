/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.GenericKernel
public import Rhone.Computation.Float64Kernel

/-! # Rational logarithm bound checks with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.LogKernel
open Float64Kernel

def powRat (x : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => powRat x n * x

def argument (x : Rat) : Rat := (x - 1) / (x + 1)

def series (x : Rat) (n : Nat) : Rat :=
  2 * GenericKernel.lsum
    (fun i => powRat (argument x) (2 * i + 1) / ((2 * i + 1 : Nat) : Rat)) n

def errorBound (x : Rat) (n : Nat) : Rat :=
  2 * powRat (absRat (argument x)) (2 * n + 1) / (1 - powRat (argument x) 2)

def normalizedSeries (u : Rat) (e : Int) (n : Nat) : Rat :=
  series u n + (e : Rat) * series 2 n

def normalizedError (u : Rat) (e : Int) (n : Nat) : Rat :=
  errorBound u n + absRat (e : Rat) * errorBound 2 n

def checkNormalized (x claimed budget : Rat) (e : Int) (n : Nat) : Bool :=
  let u := x / pow2 e
  decide (0 < x ∧ absRat (claimed - normalizedSeries u e n) + normalizedError u e n ≤ budget)

def terms : Nat := 20

def bracketCheck (x claimed budget : Rat) : Bool :=
  let e := binade x
  let step := pow2 (e - 64)
  let a := step * ((x / step).floor : Rat)
  let b := a + step
  decide (0 < a ∧ a ≤ x ∧ x ≤ b) && checkNormalized a claimed budget e terms &&
    checkNormalized b claimed budget e terms

end Rhone.Computation.LogKernel
