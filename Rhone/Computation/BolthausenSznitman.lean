/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Bolthausen-Sznitman merger rates

Source: bolthausen_sznitman1998, Prop. 1.3, eq. (1.33). -/

@[expose] public section
namespace Rhone.Computation.BolthausenSznitman

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

def mergeRate (b k : Nat) : Rat :=
  ((factorial (k - 2) * factorial (b - k) : Nat) : Rat) / ((factorial (b - 1) : Nat) : Rat)

def partialTotal (b : Nat) : Nat → Rat
  | 0 => 0
  | m + 1 => partialTotal b m +
      (if 2 ≤ m + 1 then ((choose b (m + 1) : Nat) : Rat) * mergeRate b (m + 1) else 0)

def totalRate (b : Nat) : Rat := partialTotal b b

end Rhone.Computation.BolthausenSznitman
