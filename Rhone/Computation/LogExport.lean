/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.RatRounding
public import Rhone.Computation.RationalLogBounds
/-! # Checked decimal approximation of the logarithm of a rational with an error budget -/

@[expose] public section
namespace Rhone.Computation.LogExport

def budget : Rat := 500001 / 1000000000
def decimalStep : Rat := 1 / 1000

def candidate (x : Rat) (e : Int) (n : Nat) : Rat :=
  RatRounding.quantize decimalStep
    (RationalLogBounds.normalizedSeries (x / (2 : Rat) ^ e) e n)

def checked (x : Rat) (e : Int) (n : Nat) : Option Rat :=
  let value := candidate x e n
  if RationalLogBounds.checkNormalized x value budget e n then some value else none

lemma checked_some {x value : Rat} {e : Int} {n : Nat}
    (h : checked x e n = some value) :
    value = candidate x e n ∧
      RationalLogBounds.checkNormalized x value budget e n = true := by
  dsimp only [checked] at h
  split_ifs at h with hc
  · exact ⟨(Option.some.inj h).symm, (Option.some.inj h) ▸ hc⟩

lemma checked_sound {x value : Rat} {e : Int} {n : Nat}
    (h : checked x e n = some value) :
    |(value : Real) - Real.log (x : Real)| ≤ (budget : Real) :=
  RationalLogBounds.checkNormalized_sound (checked_some h).2

lemma checked_refuses {x : Rat} {e : Int} {n : Nat}
    (h : RationalLogBounds.checkNormalized x (candidate x e n) budget e n = false) :
    checked x e n = none := by simp [checked, h]

lemma candidate_decimal (x : Rat) (e : Int) (n : Nat) :
    ∃ k : Int, candidate x e n = (k : Rat) / 1000 := by
  refine ⟨RatRounding.nearestEven
    (RationalLogBounds.normalizedSeries (x / (2 : Rat) ^ e) e n / decimalStep), ?_⟩
  unfold candidate RatRounding.quantize decimalStep
  ring

end Rhone.Computation.LogExport
