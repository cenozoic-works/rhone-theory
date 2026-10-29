/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable F-statistics and the Wahlund variance form

Source: wright1951, p. 328, p. 330. -/

@[expose] public section
namespace Rhone.Computation.FStatistics

def hweHet (p : Rat) : Rat := 2 * p * (1 - p)

def fRatio (Hobs Href : Rat) : Option Rat :=
  if Href = 0 then none else some (1 - Hobs / Href)

def fStatistics (HI HS HT : Rat) : Option (Rat × Rat × Rat) :=
  if HS = 0 ∨ HT = 0 then none
  else some (1 - HI / HS, 1 - HS / HT, 1 - HI / HT)

def sumBy {α : Type} (f : α → Rat) : List α → Rat
  | [] => 0
  | x :: xs => f x + sumBy f xs

def weightedMean (ds : List (Rat × Rat)) : Rat := sumBy (fun d => d.1 * d.2) ds

def weightedVariance (ds : List (Rat × Rat)) : Rat :=
  sumBy (fun d => d.1 * (d.2 * d.2)) ds - weightedMean ds * weightedMean ds

def pooledHet (ds : List (Rat × Rat)) : Rat := hweHet (weightedMean ds)

def meanHet (ds : List (Rat × Rat)) : Rat := sumBy (fun d => d.1 * hweHet d.2) ds

def weightsNormalized (ds : List (Rat × Rat)) : Bool := sumBy (fun d => d.1) ds == 1

def wahlundDeficit (ds : List (Rat × Rat)) : Option Rat :=
  if weightsNormalized ds then some (pooledHet ds - meanHet ds) else none

def wahlundVarianceForm (ds : List (Rat × Rat)) : Option Rat :=
  if weightsNormalized ds then some (2 * weightedVariance ds) else none

def fStWahlund (ds : List (Rat × Rat)) : Option Rat :=
  if weightsNormalized ds ∧ pooledHet ds ≠ 0 then some (2 * weightedVariance ds / pooledHet ds)
  else none

end Rhone.Computation.FStatistics
