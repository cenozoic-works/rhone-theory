/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-! # Executable stationarity check for a rational finite chain -/

@[expose] public section
namespace Rhone.Computation.Stationary

def sumBy {α : Type} (f : α → Rat) : List α → Rat
  | [] => 0
  | x :: xs => f x + sumBy f xs

def entry (Q : List (List Rat)) (x y : Nat) : Rat := (Q.getD x []).getD y 0

def comp (π : List Rat) (x : Nat) : Rat := π.getD x 0

def total (π : List Rat) : Rat := sumBy (comp π) (List.range π.length)

def vecMulColumn (Q : List (List Rat)) (π : List Rat) (y : Nat) : Rat :=
  sumBy (fun x => comp π x * entry Q x y) (List.range π.length)

def isStationary (Q : List (List Rat)) (π : List Rat) : Bool :=
  decide ((∀ x ∈ List.range π.length, 0 ≤ comp π x) ∧ total π = 1 ∧
    ∀ y ∈ List.range π.length, vecMulColumn Q π y = 0)

end Rhone.Computation.Stationary
