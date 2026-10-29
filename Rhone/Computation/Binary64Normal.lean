/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.RatRounding
/-! # Exact rational interpretation of normal binary64 words -/

@[expose] public section
namespace Rhone.Computation.Binary64Normal

def decode (bits : Nat) : Option Rat :=
  let b : Nat := bits / 2 ^ 52 % 2048
  let f : Nat := bits % 2 ^ 52
  if bits < 2 ^ 64 ∧ 1 ≤ b ∧ b ≤ 2046 then
    let v : Rat := (2 ^ 52 + f : Nat) * (2 : Rat) ^ ((b : Int) - 1075)
    some (if bits / 2 ^ 63 = 0 then v else -v)
  else none

def encode (negative : Bool) (biased fraction : Nat) : Nat :=
  (if negative then 2 ^ 63 else 0) + biased * 2 ^ 52 + fraction

lemma encode_fields (negative : Bool) {biased fraction : Nat}
    (hb : 1 ≤ biased ∧ biased ≤ 2046) (hf : fraction < 2 ^ 52) :
    encode negative biased fraction < 2 ^ 64 ∧
    encode negative biased fraction / 2 ^ 52 % 2048 = biased ∧
    encode negative biased fraction % 2 ^ 52 = fraction ∧
    encode negative biased fraction / 2 ^ 63 = (if negative then 1 else 0) := by
  cases negative <;> simp only [encode, Bool.false_eq_true, ↓reduceIte]
  all_goals norm_num at *
  all_goals omega

lemma decode_encode (negative : Bool) {biased fraction : Nat}
    (hb : 1 ≤ biased ∧ biased ≤ 2046) (hf : fraction < 2 ^ 52) :
    decode (encode negative biased fraction) =
      some (if negative then
        -((2 ^ 52 + fraction : Nat) : Rat) * (2 : Rat) ^ ((biased : Int) - 1075)
      else ((2 ^ 52 + fraction : Nat) : Rat) * (2 : Rat) ^ ((biased : Int) - 1075)) := by
  obtain ⟨hbits, hbiased, hfrac, hsign⟩ := encode_fields negative hb hf
  simp only [decode, hbiased, hfrac, hbits, hb.1, hb.2, and_self, ↓reduceIte, hsign]
  cases negative
  · simp
  · simp
    ring

lemma binade_relative {x : Rat} {e : Int} (hx : (2 : Rat) ^ e ≤ x) :
    |RatRounding.quantize ((2 : Rat) ^ (e - 52)) x - x| / x ≤ 1 / (2 : Rat) ^ 53 := by
  have hp : (0 : Rat) < 2 ^ e := zpow_pos (by norm_num) e
  have hs : (0 : Rat) < 2 ^ (e - 52) := zpow_pos (by norm_num) _
  apply RatRounding.quantize_relative hs (lt_of_lt_of_le hp hx)
  calc
    (2 : Rat) ^ (e - 52) = (2 : Rat) ^ e * (1 / (2 : Rat) ^ 52) := by
      rw [zpow_sub₀ (by norm_num)]
      norm_num
      ring
    _ ≤ x * (1 / (2 : Rat) ^ 52) := mul_le_mul_of_nonneg_right hx (by positivity)

end Rhone.Computation.Binary64Normal

namespace Rhone.Computation.Binary64Normal

def acceptedPositive (x : Rat) (bits : Nat) (e : Int) : Bool :=
  decide ((2 : Rat) ^ e ≤ x ∧ x < (2 : Rat) ^ (e + 1) ∧
    decode bits = some (RatRounding.quantize ((2 : Rat) ^ (e - 52)) x))

lemma acceptedPositive_decode {x : Rat} {bits : Nat} {e : Int}
    (h : acceptedPositive x bits e = true) :
    decode bits = some (RatRounding.quantize ((2 : Rat) ^ (e - 52)) x) := by
  simp only [acceptedPositive, decide_eq_true_eq] at h
  exact h.2.2

lemma acceptedPositive_relative {x y : Rat} {bits : Nat} {e : Int}
    (h : acceptedPositive x bits e = true) (hy : decode bits = some y) :
    |y - x| / x ≤ 1 / (2 : Rat) ^ 53 := by
  have hd := acceptedPositive_decode h
  have heq : y = RatRounding.quantize ((2 : Rat) ^ (e - 52)) x := by
    rw [hy] at hd
    exact Option.some.inj hd
  rw [heq]
  apply binade_relative
  simp only [acceptedPositive, decide_eq_true_eq] at h
  exact h.1

lemma acceptedPositive_grid_nearest {x y : Rat} {bits : Nat} {e : Int}
    (h : acceptedPositive x bits e = true) (hy : decode bits = some y) (k : Int) :
    |y - x| ≤ |(2 : Rat) ^ (e - 52) * k - x| := by
  have hd := acceptedPositive_decode h
  rw [hy] at hd
  rw [Option.some.inj hd]
  exact RatRounding.quantize_nearest (zpow_pos (by norm_num) _) x k

end Rhone.Computation.Binary64Normal
