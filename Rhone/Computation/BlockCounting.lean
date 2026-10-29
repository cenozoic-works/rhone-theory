/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable block-counting chain of Kingman's coalescent

Source: kingman1982, eq. (1.8)–(1.9). -/

@[expose] public section
namespace Rhone.Computation.BlockCounting

def rate (k : Nat) : Rat := (k : Rat) * ((k : Rat) - 1) / 2

def entry (k j : Nat) : Rat :=
  rate k * ((if j + 1 = k then 1 else 0) - (if j = k then 1 else 0))

def row (n k : Nat) : List Rat := (List.range (n + 1)).map (entry k)

def generator (n : Nat) : List (List Rat) := (List.range (n + 1)).map (row n)

end Rhone.Computation.BlockCounting
