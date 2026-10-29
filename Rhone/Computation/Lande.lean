/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Lande response `G β`

Source: lande1979, p. 406, eq. (6)–(7a); lande_arnold1983, p. 1212. -/

@[expose] public section
namespace Rhone.Computation.Lande

def sumBy {α : Type} (f : α → Rat) : List α → Rat
  | [] => 0
  | x :: xs => f x + sumBy f xs

def sumTo (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumTo f n + f n

def value (g : List Rat) (j : Nat) : Rat := g.getD j 0

def mean (f : List Rat → Rat) (gs : List (List Rat)) : Rat :=
  sumBy f gs / (gs.length : Nat)

def gEntry (gs : List (List Rat)) (j k : Nat) : Rat :=
  mean (fun g => value g j * value g k) gs -
    mean (fun g => value g j) gs * mean (fun g => value g k) gs

def responseAt (gs : List (List Rat)) (β : List Rat) (j : Nat) : Rat :=
  sumTo (fun k => gEntry gs j k * β.getD k 0) β.length

def response (gs : List (List Rat)) (β : List Rat) : List Rat :=
  (List.range β.length).map (responseAt gs β)

end Rhone.Computation.Lande
