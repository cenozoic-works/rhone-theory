/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Wright-Fisher transition probability for K alleles

Source: cannings1974, sec. 3.1, pp. 268–269; ewens2004, sec. 3.5. -/

@[expose] public section
namespace Rhone.Computation.WFKAllele

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def sumNat (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumNat f n + f n

def prodNat (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => prodNat f n * f n

def prodRat (f : Nat → Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => prodRat f n * f n

def multinomial (K : Nat) (b : Nat → Nat) : Nat :=
  fact (sumNat b K) / prodNat (fun i => fact (b i)) K

def wfMultiallele (N K : Nat) (a b : Nat → Nat) : Rat :=
  (multinomial K b : Rat) * prodRat (fun i => ((a i : Rat) / (N : Rat)) ^ (b i)) K

end Rhone.Computation.WFKAllele
