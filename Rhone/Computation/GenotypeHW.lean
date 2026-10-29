/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Hardy-Weinberg random mating

Source: hardy1908, p. 49; weinberg1908, p. 380; ewens2004, sec. 1.2. -/

@[expose] public section
namespace Rhone.Computation.GenotypeHW

def sumRange (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumRange f n + f n

def alleleFreq (K : Nat) (g : Nat → Nat → Rat) (c : Nat) : Rat :=
  (1 / 2) * sumRange (fun a => sumRange (fun b =>
    g a b * ((if a = c then 1 else 0) + (if b = c then 1 else 0))) K) K

def randomMating (K : Nat) (g : Nat → Nat → Rat) : Nat → Nat → Rat :=
  fun c d => alleleFreq K g c * alleleFreq K g d

def total (K : Nat) (g : Nat → Nat → Rat) : Rat :=
  sumRange (fun a => sumRange (fun b => g a b) K) K

def hwProportions (g : Nat → Nat → Rat) : Rat × Rat × Rat :=
  let m := randomMating 2 g
  (m 0 0, m 0 1 + m 1 0, m 1 1)

end Rhone.Computation.GenotypeHW
