/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-! # Exact supplied symmetric two-lineage island formulas -/

@[expose] public section
namespace Rhone.Computation.IslandPair

def sameTime (d : Nat) (c : Rat) : Rat := d / c

def differentTime (d : Nat) (m c : Rat) : Rat := sameTime d c + (d - 1 : Nat) / (2 * m)

def timeContrast (d : Nat) (m c : Rat) : Rat :=
  c * (d - 1 : Nat) / (2 * d * m + c * (d - 1 : Nat))

def values (d : Nat) (m c : Rat) : Array Rat :=
  #[sameTime d c, differentTime d m c, timeContrast d m c]

def check (d : Nat) (m c : Rat) (claim : Array Rat) : Bool := decide (claim = values d m c)

end Rhone.Computation.IslandPair
