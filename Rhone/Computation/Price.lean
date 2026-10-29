/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Price equation on a finite population

Source: price1970, p. 520, eq. (4); frank1995_price, p. 376, eq. (3). -/

@[expose] public section
namespace Rhone.Computation.Price

structure Parent where
  w : Rat
  z : Rat
  z' : Rat

def sumBy {α : Type} (f : α → Rat) : List α → Rat
  | [] => 0
  | x :: xs => f x + sumBy f xs

def mean (f : Parent → Rat) (l : List Parent) : Rat :=
  sumBy f l / (l.length : Nat)

def cov (f g : Parent → Rat) (l : List Parent) : Rat :=
  mean (fun p => f p * g p) l - mean f l * mean g l

def nextMean (l : List Parent) : Rat :=
  mean (fun p => p.w * p.z') l / mean (fun p => p.w) l

def meanTrait (l : List Parent) : Rat := mean (fun p => p.z) l

def selectionTerm (l : List Parent) : Rat := cov (fun p => p.w) (fun p => p.z) l

def transmissionTerm (l : List Parent) : Rat :=
  mean (fun p => p.w * (p.z' - p.z)) l

def deltaMean (l : List Parent) : Option Rat :=
  if mean (fun p => p.w) l = 0 then none else some (nextMean l - meanTrait l)

def deltaMeanPrice (l : List Parent) : Option Rat :=
  if mean (fun p => p.w) l = 0 then none
  else some ((selectionTerm l + transmissionTerm l) / mean (fun p => p.w) l)

end Rhone.Computation.Price
