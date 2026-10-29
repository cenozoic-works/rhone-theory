/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-! # Executable finite-population drift formulas -/

@[expose] public section
namespace Rhone.Computation.Drift

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def choose (n j : Nat) : Nat :=
  if j ≤ n then factorial n / (factorial j * factorial (n - j)) else 0

def wfRow (n i j : Nat) : Rat :=
  (choose n j : Rat) * ((i : Rat) / n) ^ j * (1 - (i : Rat) / n) ^ (n - j)

def moranUp (n : Nat) (r : Rat) (i : Nat) : Rat :=
  r * i * ((n : Rat) - i) / (n * (r * i + ((n : Rat) - i)))

def moranDown (n : Nat) (r : Rat) (i : Nat) : Rat :=
  (i : Rat) * ((n : Rat) - i) / (n * (r * i + ((n : Rat) - i)))

def moranRow (n : Nat) (r : Rat) (i j : Nat) : Rat :=
  (if j = i then 1 - moranUp n r i - moranDown n r i else 0)
    + (if j = i + 1 then moranUp n r i else 0)
    + (if i = j + 1 then moranDown n r i else 0)

def wfTransition (n i : Nat) : Array Rat :=
  ((List.range (n + 1)).map (wfRow n i)).toArray

def moranTransition (n : Nat) (r : Rat) (i : Nat) : Array Rat :=
  ((List.range (n + 1)).map (moranRow n r i)).toArray

def heterozygosity (n i : Nat) : Rat :=
  2 * ((i : Rat) / n) * (1 - (i : Rat) / n)

def wfHeterozygosity (n i t : Nat) : Rat :=
  (1 - 1 / (n : Rat)) ^ t * heterozygosity n i

def moranHeterozygosity (n i t : Nat) : Rat :=
  (1 - 2 / (n : Rat) ^ 2) ^ t * heterozygosity n i

def neutralFixation (n i : Nat) : Rat := (i : Rat) / n

def geometric (x : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => geometric x n + x ^ n

def moranFixation (n : Nat) (r : Rat) (i : Nat) : Rat :=
  geometric (1 / r) i / geometric (1 / r) n

end Rhone.Computation.Drift
