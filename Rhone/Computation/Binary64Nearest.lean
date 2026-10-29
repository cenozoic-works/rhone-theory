/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.RatRounding
/-! # Exact comparison across normal dyadic binades -/

@[expose] public section
namespace Rhone.Computation.Binary64Nearest

lemma binade_power (e : Int) (k : Nat) :
    (2 : Rat) ^ (e - 52) * (2 : Rat) ^ k = (2 : Rat) ^ (e - 52 + (k : Int)) := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]

lemma dyadic_lower (d : Int) {m : Nat} (hm : 2 ^ 52 ≤ m) :
    (2 : Rat) ^ d ≤ (m : Rat) * (2 : Rat) ^ (d - 52) := by
  have hmc : (2 : Rat) ^ 52 ≤ m := by exact_mod_cast hm
  have hs : (0 : Rat) ≤ 2 ^ (d - 52) := le_of_lt (zpow_pos (by norm_num) _)
  calc
    (2 : Rat) ^ d = (2 : Rat) ^ 52 * (2 : Rat) ^ (d - 52) := by
      rw [mul_comm, binade_power]
      congr 1
      norm_num
    _ ≤ (m : Rat) * (2 : Rat) ^ (d - 52) := mul_le_mul_of_nonneg_right hmc hs

lemma dyadic_upper (d : Int) {m : Nat} (hm : m < 2 ^ 53) :
    (m : Rat) * (2 : Rat) ^ (d - 52) < (2 : Rat) ^ (d + 1) := by
  have hmc : (m : Rat) < (2 : Rat) ^ 53 := by exact_mod_cast hm
  have hs : (0 : Rat) < 2 ^ (d - 52) := zpow_pos (by norm_num) _
  calc
    (m : Rat) * (2 : Rat) ^ (d - 52) < (2 : Rat) ^ 53 * (2 : Rat) ^ (d - 52) :=
      mul_lt_mul_of_pos_right hmc hs
    _ = (2 : Rat) ^ (d + 1) := by
      rw [mul_comm, binade_power]
      congr 1
      omega

lemma all_binades_nearest {x : Rat} {e : Int}
    (hlo : (2 : Rat) ^ e ≤ x) (hhi : x < (2 : Rat) ^ (e + 1))
    (d : Int) (m : Nat) (hmlo : 2 ^ 52 ≤ m) (hmhi : m < 2 ^ 53) :
    |RatRounding.quantize ((2 : Rat) ^ (e - 52)) x - x| ≤
      |(m : Rat) * (2 : Rat) ^ (d - 52) - x| := by
  have hs : (0 : Rat) < 2 ^ (e - 52) := zpow_pos (by norm_num) _
  rcases lt_trichotomy d e with hlt | heq | hgt
  · have hsep : d + 1 ≤ e := by omega
    have hy : (m : Rat) * (2 : Rat) ^ (d - 52) ≤ (2 : Rat) ^ e :=
      (dyadic_upper d hmhi).le.trans (zpow_le_zpow_right₀ (by norm_num) hsep)
    have hnear := RatRounding.quantize_nearest hs x (2 ^ 52)
    have hpoint : (2 : Rat) ^ (e - 52) * ((2 ^ 52 : Int) : Rat) = (2 : Rat) ^ e := by
      calc
        (2 : Rat) ^ (e - 52) * ((2 ^ 52 : Int) : Rat) =
            (2 : Rat) ^ (e - 52) * (2 : Rat) ^ 52 := by norm_num
        _ = (2 : Rat) ^ (e - 52 + (52 : Int)) := binade_power e 52
        _ = (2 : Rat) ^ e := by congr 1; omega
    rw [hpoint] at hnear
    calc
      _ ≤ |(2 : Rat) ^ e - x| := hnear
      _ ≤ |(m : Rat) * (2 : Rat) ^ (d - 52) - x| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hlo), abs_of_nonpos (sub_nonpos.mpr (hy.trans hlo))]
        linarith
  · subst d
    simpa [mul_comm] using RatRounding.quantize_nearest hs x (m : Int)
  · have hsep : e + 1 ≤ d := by omega
    have hy : (2 : Rat) ^ (e + 1) ≤ (m : Rat) * (2 : Rat) ^ (d - 52) :=
      (zpow_le_zpow_right₀ (by norm_num) hsep).trans (dyadic_lower d hmlo)
    have hnear := RatRounding.quantize_nearest hs x (2 ^ 53)
    have hpoint : (2 : Rat) ^ (e - 52) * ((2 ^ 53 : Int) : Rat) = (2 : Rat) ^ (e + 1) := by
      calc
        (2 : Rat) ^ (e - 52) * ((2 ^ 53 : Int) : Rat) =
            (2 : Rat) ^ (e - 52) * (2 : Rat) ^ 53 := by norm_num
        _ = (2 : Rat) ^ (e - 52 + (53 : Int)) := binade_power e 53
        _ = (2 : Rat) ^ (e + 1) := by congr 1; omega
    rw [hpoint] at hnear
    calc
      _ ≤ |(2 : Rat) ^ (e + 1) - x| := hnear
      _ ≤ |(m : Rat) * (2 : Rat) ^ (d - 52) - x| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hhi.le), abs_of_nonneg (sub_nonneg.mpr (hhi.le.trans hy))]
        linarith

end Rhone.Computation.Binary64Nearest
