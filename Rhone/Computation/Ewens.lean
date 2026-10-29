/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Ewens sampling quantities

Source: ewens1972, eq. (11), (22)–(23), (30), pp. 91, 95, 102; durrett2008, Thm 1.11; ewens2004,
sec. 3. -/

@[expose] public section
namespace Rhone.Computation.Ewens

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def risingFactorial (θ : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => risingFactorial θ n * (θ + n)

def stirlingStep (n : Nat) (row : List Nat) : List Nat :=
  List.zipWith (· + ·) (row.map (n * ·) ++ [0]) (0 :: row)

def stirlingRow : Nat → List Nat
  | 0 => [1]
  | n + 1 => stirlingStep n (stirlingRow n)

def stirling (n k : Nat) : Nat := (stirlingRow n).getD k 0

def classFactor (θ : Rat) (parts : List Nat) (j : Nat) : Rat :=
  (θ / (j : Rat)) ^ parts.count j / ((factorial (parts.count j) : Nat) : Rat)

def classProduct (θ : Rat) (parts : List Nat) : Nat → Rat
  | 0 => 1
  | m + 1 => classProduct θ parts m * classFactor θ parts (m + 1)

def esf (θ : Rat) (parts : List Nat) : Option Rat :=
  if θ ≤ 0 ∨ parts.any (· == 0) then none
  else some ((factorial parts.sum : Nat) / risingFactorial θ parts.sum *
    classProduct θ parts parts.sum)

def alleleCountProb (θ : Rat) (n k : Nat) : Option Rat :=
  if θ ≤ 0 then none else some ((stirling n k : Nat) * θ ^ k / risingFactorial θ n)

def harmonicSum (θ : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => harmonicSum θ n + θ / (θ + n)

def expectedAlleles (θ : Rat) (n : Nat) : Option Rat :=
  if θ ≤ 0 then none else some (harmonicSum θ n)

end Rhone.Computation.Ewens
