/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.Binary64Encode
public import Rhone.Computation.Binary64Nearest
/-! # Even word parity at exact binary64 rounding ties -/

@[expose] public section
namespace Rhone.Computation.Binary64TieEven

lemma nearest_floor (x : Rat) : Int.floor x ≤ RatRounding.nearestEven x := by
  dsimp only [RatRounding.nearestEven]
  split_ifs <;> omega

lemma binade_index_lower {x : Rat} {e : Int} (hlo : (2 : Rat) ^ e ≤ x) :
    (2 : Int) ^ 52 ≤ RatRounding.nearestEven (x / (2 : Rat) ^ (e - 52)) := by
  have hs : (0 : Rat) < 2 ^ (e - 52) := zpow_pos (by norm_num) _
  have hp : ((2 : Int) ^ 52 : Rat) * (2 : Rat) ^ (e - 52) = (2 : Rat) ^ e := by
    calc
      _ = (2 : Rat) ^ (e - 52) * (2 : Rat) ^ 52 := by norm_num; ring
      _ = (2 : Rat) ^ (e - 52 + (52 : Int)) := Binary64Nearest.binade_power e 52
      _ = (2 : Rat) ^ e := by congr 1; omega
  have hindex : ((2 : Int) ^ 52 : Rat) ≤ x / (2 : Rat) ^ (e - 52) :=
    (le_div_iff₀ hs).mpr (by rw [hp]; exact hlo)
  exact (Int.le_floor.mpr hindex).trans (nearest_floor _)

lemma word_even_of_index_even {x : Rat} {e : Int}
    (hlo : (2 : Int) ^ 52 ≤ RatRounding.nearestEven (x / (2 : Rat) ^ (e - 52)))
    (heven : RatRounding.nearestEven (x / (2 : Rat) ^ (e - 52)) % 2 = 0) :
    Binary64Encode.word x e % 2 = 0 := by
  dsimp only [Binary64Encode.word, Binary64Normal.encode]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  split_ifs with hcarry
  · norm_num [Nat.add_mod, Nat.mul_mod]
  · have hm : 0 ≤ RatRounding.nearestEven (x / (2 : Rat) ^ (e - 52)) - 2 ^ 52 := by
      exact sub_nonneg.mpr hlo
    have hc := Int.toNat_of_nonneg hm
    have hpar : (RatRounding.nearestEven (x / (2 : Rat) ^ (e - 52)) - 2 ^ 52).toNat % 2 = 0 := by
      norm_num at hlo heven hc ⊢
      omega
    rw [Nat.add_mod, Nat.mul_mod]
    simpa using hpar

lemma word_tie_even {x : Rat} {e : Int} (hlo : (2 : Rat) ^ e ≤ x)
    (htie : x / (2 : Rat) ^ (e - 52) -
      (Int.floor (x / (2 : Rat) ^ (e - 52)) : Rat) = 1 / 2) :
    Binary64Encode.word x e % 2 = 0 :=
  word_even_of_index_even (binade_index_lower hlo) (RatRounding.nearestEven_tie _ htie)

end Rhone.Computation.Binary64TieEven
