/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable effective population size

Source: wright1931, pp. 108–109; felsenstein1971, pp. 582–585. -/

@[expose] public section
namespace Rhone.Computation.EffectiveSize

def sumBy {α : Type} (f : α → Rat) : List α → Rat
  | [] => 0
  | x :: xs => f x + sumBy f xs

def harmonicMean (sizes : List Rat) : Option Rat :=
  if sizes.isEmpty ∨ sizes.any (fun x => decide (x ≤ 0)) then none
  else some ((sizes.length : Nat) / sumBy (fun x => 1 / x) sizes)

def unequalSexEffective (Nm Nf : Nat) : Option Rat :=
  if Nm = 0 ∨ Nf = 0 then none
  else some (4 * (Nm : Rat) * (Nf : Rat) / ((Nm : Rat) + (Nf : Rat)))

def varianceEffective (p v : Rat) : Option Rat :=
  if 0 < p ∧ p < 1 ∧ 0 < v then some (p * (1 - p) / (2 * v)) else none

def offspringVarianceEffective (N : Nat) (sigma2 : Rat) : Option Rat :=
  if 2 ≤ N ∧ 0 < sigma2 then some (((N : Rat) - 1) / (2 * sigma2)) else none

end Rhone.Computation.EffectiveSize
