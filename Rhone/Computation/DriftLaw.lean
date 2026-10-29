/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Absorption

/-! # Executable law of the allele count after a number of steps -/

@[expose] public section
namespace Rhone.Computation.Drift

def pointLaw (n i : Nat) : Array Rat :=
  ((List.range (n + 1)).map fun j => if j = i then (1 : Rat) else 0).toArray

def stepLaw (n : Nat) (row : Nat → Nat → Rat) (law : Array Rat) : Array Rat :=
  ((List.range (n + 1)).map fun j =>
    Absorption.sum (fun k => law.getD k 0 * row k j) (n + 1)).toArray

def lawAfter (n : Nat) (row : Nat → Nat → Rat) (i : Nat) : Nat → Array Rat
  | 0 => pointLaw n i
  | t + 1 => stepLaw n row (lawAfter n row i t)

def lawHeterozygosity (n : Nat) (law : Array Rat) : Rat :=
  Absorption.sum (fun j => law.getD j 0 * heterozygosity n j) (n + 1)

def kernelEntry (kernel : Array (Array Rat)) (k j : Nat) : Rat :=
  (kernel.getD k #[]).getD j 0

def wfDistribution (n i t : Nat) : Array Rat :=
  lawAfter n (kernelEntry (Absorption.wfKernel n)) i t

def moranDistribution (n : Nat) (r : Rat) (i t : Nat) : Array Rat :=
  lawAfter n (kernelEntry (Absorption.moranKernel n r)) i t

end Rhone.Computation.Drift
