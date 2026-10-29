/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Fisher partial change and additive variance

Source: ewens_lessard2015, p. 61, eq. 11–13; ewens1989, pp. 175–177, eq. (22)–(28). -/

@[expose] public section
namespace Rhone.Computation.FisherFundamental

structure Genotype where
  p : Rat
  W : Rat
  x : List Rat

def sumBy {α : Type} (f : α → Rat) : List α → Rat
  | [] => 0
  | x :: xs => f x + sumBy f xs

def sumTo (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumTo f n + f n

def count (g : Genotype) (k : Nat) : Rat := g.x.getD k 0

def meanFitness (gs : List Genotype) : Rat := sumBy (fun g => g.p * g.W) gs

def alleleFreq (gs : List Genotype) (k : Nat) : Rat :=
  sumBy (fun g => g.p * count g k) gs / 2

def selectedFreq (gs : List Genotype) (k : Nat) : Rat :=
  sumBy (fun g => g.p * g.W / meanFitness gs * count g k) gs / 2

def score (β : List Rat) (g : Genotype) : Rat :=
  sumTo (fun k => count g k * β.getD k 0) β.length

def partialChange (gs : List Genotype) (β : List Rat) : Option Rat :=
  if meanFitness gs = 0 then none
  else some (2 * sumTo (fun k => (selectedFreq gs k - alleleFreq gs k) * β.getD k 0) β.length)

def additiveVar (gs : List Genotype) (β : List Rat) : Rat :=
  sumBy (fun g => g.p * (score β g - meanFitness gs) ^ 2) gs

def varianceOverMean (gs : List Genotype) (β : List Rat) : Option Rat :=
  if meanFitness gs = 0 then none else some (additiveVar gs β / meanFitness gs)

end Rhone.Computation.FisherFundamental
