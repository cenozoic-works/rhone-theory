/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.RatRounding
/-! # Exact integer quotient and remainder rounding -/

@[expose] public section
namespace Rhone.Computation.IntegerRounding

def quotientNearest (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if den < 2 * r then q + 1
  else if 2 * r = den then q + q % 2
  else q

lemma fraction_decompose (num : Nat) {den : Nat} (hd : 0 < den) :
    (num : Rat) / den = (num / den : Nat) + (num % den : Nat) / (den : Rat) := by
  have he := Nat.mod_add_div num den
  have hc := congrArg (fun k : Nat => (k : Rat)) he
  simp only [Nat.cast_add, Nat.cast_mul] at hc
  have hd' : (den : Rat) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  apply (div_eq_iff hd').mpr
  field_simp
  nlinarith

lemma floor_fraction (num : Nat) {den : Nat} (hd : 0 < den) :
    Int.floor ((num : Rat) / den) = (num / den : Nat) := by
  rw [Int.floor_eq_iff]
  rw [fraction_decompose num hd]
  have hr : ((num % den : Nat) : Rat) < den := by exact_mod_cast Nat.mod_lt num hd
  have hd' : (0 : Rat) < den := by exact_mod_cast hd
  constructor
  · simp only [Int.cast_natCast]
    have hr0 : (0 : Rat) ≤ ((num % den : Nat) : Rat) / den := by positivity
    linarith
  · simp only [Int.cast_natCast]
    have he : ((num % den : Nat) : Rat) / den < 1 := (div_lt_one hd').mpr hr
    linarith

lemma quotientNearest_eq (num : Nat) {den : Nat} (hd : 0 < den) :
    (quotientNearest num den : Int) = RatRounding.nearestEven ((num : Rat) / den) := by
  have hf := floor_fraction num hd
  have hx := fraction_decompose num hd
  have hd' : (0 : Rat) < den := by exact_mod_cast hd
  have hlo : ((num : Rat) / den - (num / den : Nat)) < 1 / 2 ↔
      2 * (num % den) < den := by
    rw [hx]
    have h : ((num % den : Nat) : Rat) / den < 1 / 2 ↔
      (2 : Rat) * ((num % den : Nat) : Rat) < den := by
      rw [div_lt_iff₀ hd']
      constructor <;> intro h <;> linarith
    have hn : (2 : Rat) * ((num % den : Nat) : Rat) < (den : Rat) ↔ 2 * (num % den) < den := by
      norm_cast
    simpa only [add_sub_cancel_left] using h.trans hn
  have hhi : (1 / 2 : Rat) < (num : Rat) / den - (num / den : Nat) ↔
      den < 2 * (num % den) := by
    rw [hx]
    have h : (1 / 2 : Rat) < ((num % den : Nat) : Rat) / den ↔
      (den : Rat) < 2 * ((num % den : Nat) : Rat) := by
      rw [lt_div_iff₀ hd']
      constructor <;> intro h <;> linarith
    have hn : (den : Rat) < 2 * ((num % den : Nat) : Rat) ↔ den < 2 * (num % den) := by
      norm_cast
    simpa only [add_sub_cancel_left] using h.trans hn
  unfold RatRounding.nearestEven quotientNearest
  rw [hf]
  simp only [Int.cast_natCast]
  simp only [hlo, hhi]
  split_ifs
  all_goals try simp only [Nat.cast_add, Nat.cast_ofNat, Int.natCast_mod]
  all_goals omega

end Rhone.Computation.IntegerRounding
