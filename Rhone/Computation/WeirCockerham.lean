/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Weir-Cockerham variance components for the haploid design

Source: weir_cockerham1984, pp. 1362–1363. -/

@[expose] public section
namespace Rhone.Computation.WeirCockerham

def sumBy {α : Type} (f : α → Rat) : List α → Rat
  | [] => 0
  | x :: xs => f x + sumBy f xs

def popCount (s : List (Nat × Nat)) : Rat := (s.length : Rat)

def totalN (s : List (Nat × Nat)) : Rat := sumBy (fun d => (d.1 : Rat)) s

def sumSqN (s : List (Nat × Nat)) : Rat := sumBy (fun d => (d.1 : Rat) ^ 2) s

def ncBar (s : List (Nat × Nat)) : Rat :=
  (totalN s - sumSqN s / totalN s) / (popCount s - 1)

def pBar (s : List (Nat × Nat)) : Rat := sumBy (fun d => (d.2 : Rat)) s / totalN s

def msp (s : List (Nat × Nat)) : Rat :=
  sumBy (fun d => (d.1 : Rat) * ((d.2 : Rat) / (d.1 : Rat) - pBar s) ^ 2) s / (popCount s - 1)

def msg (s : List (Nat × Nat)) : Rat :=
  sumBy (fun d => (d.1 : Rat) * ((d.2 : Rat) / (d.1 : Rat)) * (1 - (d.2 : Rat) / (d.1 : Rat))) s /
    (totalN s - popCount s)

def wcA (s : List (Nat × Nat)) : Rat := (msp s - msg s) / ncBar s

def wcB (s : List (Nat × Nat)) : Rat := msg s

def wcTotal (s : List (Nat × Nat)) : Rat := wcA s + wcB s

end Rhone.Computation.WeirCockerham
