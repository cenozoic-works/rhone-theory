/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-! # Executable Stirling numbers of the second kind -/

@[expose] public section
namespace Rhone.Computation.Stirling

def secondStep (row : List Nat) : List Nat :=
  List.zipWith (· + ·) (List.zipWith (· * ·) (List.range (row.length + 1)) (row ++ [0]))
    (0 :: row)

def secondRow : Nat → List Nat
  | 0 => [1]
  | n + 1 => secondStep (secondRow n)

def second (n k : Nat) : Nat := (secondRow n).getD k 0

end Rhone.Computation.Stirling
