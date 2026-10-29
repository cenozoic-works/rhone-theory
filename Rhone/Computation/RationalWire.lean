/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Init

/-! # Exact ASCII rational wire codec -/

@[expose] public section
namespace Rhone.Computation.RationalWire

def decimal (xs : List Char) : Nat :=
  xs.foldl (fun n ch => 10 * n + (ch.toNat - '0'.toNat)) 0

def digits (xs : List Char) : Except String Nat :=
  if xs.isEmpty || !xs.all Char.isDigit then .error "invalid decimal digits"
  else .ok (decimal xs)

def integer (xs : List Char) : Except String Int := do
  if xs.head? == some '-' then
    let n ← (digits xs.tail).mapError (fun _ => "invalid numerator")
    return -(n : Int)
  else
    let n ← (digits xs).mapError (fun _ => "invalid numerator")
    return (n : Int)

def decodeChars (xs : List Char) : Except String Rat := do
  let parts := xs.splitOn '/'
  let numerator ← integer (parts.head?.getD [])
  match parts with
  | [_] => return (numerator : Rat)
  | [_, d] =>
    let denominator ← (digits d).mapError (fun _ => "invalid denominator")
    if denominator == 0 then throw "zero denominator"
    return mkRat numerator denominator
  | _ => throw "invalid fraction"

def decode (s : String) : Except String Rat := decodeChars s.toList

def intChars : Int → List Char
  | .ofNat n => Nat.toDigits 10 n
  | .negSucc n => '-' :: Nat.toDigits 10 (n + 1)

def strictPrint (r : Rat) : String :=
  String.ofList (intChars r.num ++ '/' :: Nat.toDigits 10 r.den)

end Rhone.Computation.RationalWire
