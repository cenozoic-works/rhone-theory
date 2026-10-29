/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Kinship

/-!
# Executable Wright path sum on a finite pedigree

Source: wright1922, p. 334. -/

@[expose] public section
namespace Rhone.Computation.WrightPath
open Kinship

def sumBy {α : Type} (f : α → Rat) : List α → Rat
  | [] => 0
  | x :: xs => f x + sumBy f xs

def parentAt (ped : Ped) (i : Nat) (s : Fin 2) : Option Nat :=
  (parents ped i).map fun p => if s = 0 then p.1 else p.2

def branch (ped : Ped) (rest : Nat → List (List (Fin 2))) (i : Nat) (s : Fin 2) :
    List (List (Fin 2)) :=
  match parentAt ped i s with
  | none => []
  | some p => (rest p).map (List.cons s)

def chainsF (ped : Ped) : Nat → Nat → Nat → List (List (Fin 2))
  | 0, _, _ => []
  | f + 1, i, a =>
    (if i = a then [[]] else []) ++
      (branch ped (fun p => chainsF ped f p a) i 0 ++ branch ped (fun p => chainsF ped f p a) i 1)

def chains (ped : Ped) (i a : Nat) : List (List (Fin 2)) := chainsF ped (i + 1) i a

def visited (ped : Ped) (i : Nat) : List (Fin 2) → List Nat
  | [] => [i]
  | s :: l =>
    i :: (match parentAt ped i s with
      | none => []
      | some p => visited ped p l)

def pathSum (ped : Ped) (n i j : Nat) : Rat :=
  sumBy (fun a => sumBy (fun c₁ => sumBy (fun c₂ =>
    if (visited ped i c₁).all (fun x => !(visited ped j c₂).contains x || x == a) then
      (1 / 2 : Rat) ^ (c₁.length + c₂.length + 1) * (1 + inbreeding ped a)
    else 0) (chains ped j a)) (chains ped i a)) (List.range n)

end Rhone.Computation.WrightPath
