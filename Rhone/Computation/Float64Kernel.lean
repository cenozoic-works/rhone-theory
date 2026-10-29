/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Config

/-! # Binary64 rounding checks with core-library definitions only -/

@[expose] public section
namespace Rhone.Computation.Float64Kernel

def pow2 (e : Int) : Rat :=
  if 0 ≤ e then ((2 ^ e.toNat : Nat) : Rat) else 1 / ((2 ^ (-e).toNat : Nat) : Rat)

def absRat (x : Rat) : Rat := if x < 0 then -x else x

def nearestEven (x : Rat) : Int :=
  let z := x.floor
  if x - z < 1 / 2 then z
  else if 1 / 2 < x - z then z + 1
  else if z % 2 = 0 then z else z + 1

def quantize (step x : Rat) : Rat := step * nearestEven (x / step)

def decodeNormal (bits : Nat) : Option Rat :=
  let b : Nat := bits / 2 ^ 52 % 2048
  let f : Nat := bits % 2 ^ 52
  if bits < 2 ^ 64 ∧ 1 ≤ b ∧ b ≤ 2046 then
    let v : Rat := ((2 ^ 52 + f : Nat) : Rat) * pow2 ((b : Int) - 1075)
    some (if bits / 2 ^ 63 = 0 then v else -v)
  else none

def decodeFinite (bits : Nat) : Option Rat :=
  let b : Nat := bits / 2 ^ 52 % 2048
  let f : Nat := bits % 2 ^ 52
  if bits < 2 ^ 64 ∧ b < 2047 then
    if b = 0 then
      let value : Rat := (f : Rat) * pow2 (-1074)
      some (if bits / 2 ^ 63 = 0 then value else -value)
    else decodeNormal bits
  else none

def encode (negative : Bool) (biased fraction : Nat) : Nat :=
  (if negative then 2 ^ 63 else 0) + biased * 2 ^ 52 + fraction

def acceptedPositive (x : Rat) (bits : Nat) (e : Int) : Bool :=
  decide (pow2 e ≤ x ∧ x < pow2 (e + 1) ∧
    decodeNormal bits = some (quantize (pow2 (e - 52)) x))

def accepted (x : Rat) (bits : Nat) (e : Int) : Bool :=
  decide (x = 0 ∧ bits = 0) || acceptedPositive x bits e

def guardedAccepted (x : Rat) (bits : Nat) (e : Int) : Bool :=
  if x = 0 then decide (bits = 0)
  else if e < -1023 ∨ 1023 < e then false
  else accepted x bits e

def binade (x : Rat) : Int :=
  let e0 : Int := (Nat.log2 x.num.natAbs : Int) - (Nat.log2 x.den : Int)
  if pow2 e0 ≤ x then (if x < pow2 (e0 + 1) then e0 else e0 + 1) else e0 - 1

def word (x : Rat) (e : Int) : Nat :=
  let m := nearestEven (x / pow2 (e - 52))
  let carried := m = (2 : Int) ^ 53
  let finalExponent := if carried then e + 1 else e
  let finalMantissa := if carried then (2 : Int) ^ 52 else m
  encode false (finalExponent + 1023).toNat (finalMantissa - 2 ^ 52).toNat

def nearestWord (x : Rat) : Nat := if x = 0 then 0 else word x (binade x)

structure Cell where
  original : Rat
  word : Nat
  exponent : Int

def Cell.accepted (cell : Cell) : Bool := guardedAccepted cell.original cell.word cell.exponent

def Cell.relativeError (cell : Cell) : Rat :=
  match decodeFinite cell.word with
  | some value => absRat (value - cell.original) / cell.original
  | none => 0

def maxRelativeError (cells : List Cell) : Rat :=
  (cells.map Cell.relativeError).foldr max 0

def cellsAccepted (cells : List Cell) : Bool := cells.all Cell.accepted

end Rhone.Computation.Float64Kernel
