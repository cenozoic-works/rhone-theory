/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Drift
public import Init.Data.Nat.Lemmas

/-! # Exact first-step certificates for complete discrete absorption-time tables -/

@[expose] public section
namespace Rhone.Computation.Absorption

def sum (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | k + 1 => sum f k + f k

abbrev ValidTable (n : Nat) (row : Nat → Nat → Rat) (table : Array Rat) : Prop :=
  table.size = n + 1 ∧ ∀ i : Fin (n + 1),
    table.getD i 0 = if i.val = 0 ∨ i.val = n then 0
      else 1 + sum (fun j => row i j * table.getD j 0) (n + 1)

def check (n : Nat) (row : Nat → Nat → Rat) (table : Array Rat) : Bool :=
  decide (ValidTable n row table)

def checkWf (n : Nat) (table : Array Rat) : Bool :=
  check n (Drift.wfRow n) table

def checkMoran (n : Nat) (r : Rat) (table : Array Rat) : Bool :=
  check n (Drift.moranRow n r) table

def wfKernel (n : Nat) : Array (Array Rat) :=
  ((List.range (n + 1)).map (Drift.wfTransition n)).toArray

def moranKernel (n : Nat) (r : Rat) : Array (Array Rat) :=
  ((List.range (n + 1)).map (Drift.moranTransition n r)).toArray

def checkWfReport (n : Nat) (kernel : Array (Array Rat)) (table : Array Rat) : Bool :=
  decide (kernel = wfKernel n) && checkWf n table

def checkMoranReport (n : Nat) (r : Rat) (kernel : Array (Array Rat))
    (table : Array Rat) : Bool :=
  decide (kernel = moranKernel n r) && checkMoran n r table

end Rhone.Computation.Absorption
