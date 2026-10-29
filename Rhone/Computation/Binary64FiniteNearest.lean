/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.Binary64Normal
public import Rhone.Computation.Binary64WordNearest
/-! # Nearest comparison against every finite binary64 word -/

@[expose] public section
namespace Rhone.Computation.Binary64FiniteNearest

lemma normal_positive_min {bits : Nat} {y : Rat}
    (h : Binary64Normal.decode bits = some y) (hy : 0 < y) :
    (2 : Rat) ^ (-1022 : Int) ≤ y := by
  have hf : bits % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  dsimp only [Binary64Normal.decode] at h
  split_ifs at h with hv hs
  · have hd : (-1022 : Int) ≤ ((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1023 := by omega
    have hm : 2 ^ 52 ≤ 2 ^ 52 + bits % 2 ^ 52 := by omega
    have hlo := Binary64Nearest.dyadic_lower
      (((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1023) hm
    have heq : ((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1023 - 52 =
        ((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1075 := by omega
    rw [heq] at hlo
    rw [← Option.some.inj h]
    exact (zpow_le_zpow_right₀ (by norm_num) hd).trans hlo
  · have hp : (0 : Rat) ≤ ((2 ^ 52 + bits % 2 ^ 52 : Nat) : Rat) *
        (2 : Rat) ^ (((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1075) := by positivity
    rw [← Option.some.inj h] at hy
    linarith

lemma accepted_lower_exponent {x y : Rat} {bits : Nat} {e : Int}
    (h : Binary64Normal.acceptedPositive x bits e = true)
    (hy : Binary64Normal.decode bits = some y) : -1023 ≤ e := by
  have hc := Binary64Normal.acceptedPositive_decode h
  rw [hy] at hc
  have hdom := h
  simp only [Binary64Normal.acceptedPositive, decide_eq_true_eq] at hdom
  have hx : (0 : Rat) < x := lt_of_lt_of_le (zpow_pos (by norm_num) _) hdom.1
  have hs : (0 : Rat) < 2 ^ (e - 52) := zpow_pos (by norm_num) _
  have hp : (0 : Rat) < y := by
    rw [Option.some.inj hc]
    have hr := RatRounding.quantize_relative hs hx (by
      calc
        (2 : Rat) ^ (e - 52) = (2 : Rat) ^ e * (1 / (2 : Rat) ^ 52) := by
          rw [zpow_sub₀ (by norm_num)]
          norm_num
          ring
        _ ≤ x * (1 / (2 : Rat) ^ 52) :=
          mul_le_mul_of_nonneg_right hdom.1 (by positivity))
    have he := (div_le_iff₀ hx).mp hr
    have ha := (abs_le.mp he).1
    have hh : (1 / (2 : Rat) ^ 53) < 1 := by norm_num
    nlinarith
  have hlo := normal_positive_min hy hp
  have hn := RatRounding.quantize_nearest hs x (2 ^ 53)
  have hg : (2 : Rat) ^ (e - 52) * ((2 ^ 53 : Int) : Rat) = (2 : Rat) ^ (e + 1) := by
    calc
      _ = (2 : Rat) ^ (e - 52) * (2 : Rat) ^ 53 := by norm_num
      _ = (2 : Rat) ^ (e - 52 + (53 : Int)) := Binary64Nearest.binade_power e 53
      _ = (2 : Rat) ^ (e + 1) := by congr 1; omega
  rw [hg, ← Option.some.inj hc, abs_of_nonneg (sub_nonneg.mpr hdom.2.1.le)] at hn
  have hb : y ≤ (2 : Rat) ^ (e + 1) := by
    have ha := le_abs_self (y - x)
    linarith
  have he := (zpow_le_zpow_iff_right₀ (show (1 : Rat) < 2 by norm_num)).mp (hlo.trans hb)
  omega

end Rhone.Computation.Binary64FiniteNearest

namespace Rhone.Computation.Binary64FiniteNearest

lemma accepted_decoded_positive {x y : Rat} {bits : Nat} {e : Int}
    (h : Binary64Normal.acceptedPositive x bits e = true)
    (hy : Binary64Normal.decode bits = some y) : 0 < y := by
  have hdom := h
  simp only [Binary64Normal.acceptedPositive, decide_eq_true_eq] at hdom
  have hx : (0 : Rat) < x := lt_of_lt_of_le (zpow_pos (by norm_num) _) hdom.1
  have he := (div_le_iff₀ hx).mp (Binary64Normal.acceptedPositive_relative h hy)
  have ha := (abs_le.mp he).1
  have hh : (1 / (2 : Rat) ^ 53) < 1 := by norm_num
  nlinarith

lemma accepted_subnormal_nearest {x y : Rat} {bits : Nat} {e : Int}
    (h : Binary64Normal.acceptedPositive x bits e = true)
    (hy : Binary64Normal.decode bits = some y) (m : Nat) (hm : m < 2 ^ 52) :
    |y - x| ≤ |(m : Rat) * (2 : Rat) ^ (-1074 : Int) - x| := by
  have hc := Binary64Normal.acceptedPositive_decode h
  rw [hy] at hc
  have hdom := h
  simp only [Binary64Normal.acceptedPositive, decide_eq_true_eq] at hdom
  have hemin := accepted_lower_exponent h hy
  have hstep : (0 : Rat) < 2 ^ (e - 52) := zpow_pos (by norm_num) _
  have hquantum : (0 : Rat) < 2 ^ (-1074 : Int) := zpow_pos (by norm_num) _
  have hmax : (m : Rat) * (2 : Rat) ^ (-1074 : Int) ≤
      (2 : Rat) ^ (-1022 : Int) - (2 : Rat) ^ (-1074 : Int) := by
    have hnat : m + 1 ≤ 2 ^ 52 := by omega
    have hcast : (m : Rat) + 1 ≤ (2 : Rat) ^ 52 := by exact_mod_cast hnat
    have hp := mul_le_mul_of_nonneg_right hcast hquantum.le
    have heq : (2 : Rat) ^ 52 * (2 : Rat) ^ (-1074 : Int) =
        (2 : Rat) ^ (-1022 : Int) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
    rw [add_mul, one_mul, heq] at hp
    linarith
  rcases (show e = -1023 ∨ -1022 ≤ e by omega) with heq | hlarge
  · subst e
    have hxT : x < (2 : Rat) ^ (-1022 : Int) := by simpa using hdom.2.1
    have hmin := normal_positive_min hy (accepted_decoded_positive h hy)
    have hnear := RatRounding.quantize_nearest hstep x (2 ^ 53)
    have hpoint : (2 : Rat) ^ ((-1023 : Int) - 52) * ((2 ^ 53 : Int) : Rat) =
        (2 : Rat) ^ (-1022 : Int) := by
      calc
        _ = (2 : Rat) ^ ((-1023 : Int) - 52) * (2 : Rat) ^ 53 := by norm_num
        _ = (2 : Rat) ^ ((-1023 : Int) - 52 + (53 : Int)) :=
          Binary64Nearest.binade_power (-1023) 53
    rw [hpoint, ← Option.some.inj hc] at hnear
    rw [abs_of_nonneg (sub_nonneg.mpr (hxT.le.trans hmin)),
      abs_of_nonneg (sub_nonneg.mpr hxT.le)] at hnear
    have hyT : y = (2 : Rat) ^ (-1022 : Int) := by linarith
    have herr := RatRounding.quantize_error hstep x
    rw [← Option.some.inj hc, hyT, abs_of_nonneg (sub_nonneg.mpr hxT.le)] at herr
    have hscale : (2 : Rat) ^ ((-1023 : Int) - 52) / 2 =
        (2 : Rat) ^ (-1074 : Int) / 4 := by
      change (2 : Rat) ^ (-1075 : Int) / 2 = (2 : Rat) ^ (-1074 : Int) / 4
      have h2 : (2 : Rat)⁻¹ = (2 : Rat) ^ (-1 : Int) := by norm_num
      have h4 : (4 : Rat)⁻¹ = (2 : Rat) ^ (-2 : Int) := by norm_num
      rw [div_eq_mul_inv, div_eq_mul_inv, h2, h4,
        ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
      congr 1
    rw [hscale] at herr
    rw [hyT, abs_of_nonneg (sub_nonneg.mpr hxT.le), abs_of_nonpos (by linarith)]
    linarith
  · have hL : (2 : Rat) ^ (-1022 : Int) ≤ (2 : Rat) ^ e :=
      zpow_le_zpow_right₀ (by norm_num) hlarge
    have hzL : (m : Rat) * (2 : Rat) ^ (-1074 : Int) ≤ (2 : Rat) ^ e := by linarith
    have hnear := RatRounding.quantize_nearest hstep x (2 ^ 52)
    have hpoint : (2 : Rat) ^ (e - 52) * ((2 ^ 52 : Int) : Rat) = (2 : Rat) ^ e := by
      calc
        _ = (2 : Rat) ^ (e - 52) * (2 : Rat) ^ 52 := by norm_num
        _ = (2 : Rat) ^ (e - 52 + (52 : Int)) := Binary64Nearest.binade_power e 52
        _ = (2 : Rat) ^ e := by congr 1; omega
    rw [hpoint, ← Option.some.inj hc] at hnear
    calc
      _ ≤ |(2 : Rat) ^ e - x| := hnear
      _ ≤ |(m : Rat) * (2 : Rat) ^ (-1074 : Int) - x| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hdom.1),
          abs_of_nonpos (sub_nonpos.mpr (hzL.trans hdom.1))]
        linarith

end Rhone.Computation.Binary64FiniteNearest

namespace Rhone.Computation.Binary64FiniteNearest

def decodeFinite (bits : Nat) : Option Rat :=
  let b : Nat := bits / 2 ^ 52 % 2048
  let f : Nat := bits % 2 ^ 52
  if bits < 2 ^ 64 ∧ b < 2047 then
    if b = 0 then
      let value : Rat := (f : Rat) * (2 : Rat) ^ (-1074 : Int)
      some (if bits / 2 ^ 63 = 0 then value else -value)
    else Binary64Normal.decode bits
  else none

lemma finite_classes {bits : Nat} {z : Rat} (h : decodeFinite bits = some z) :
    Binary64Normal.decode bits = some z ∨
    ∃ m : Nat, m < 2 ^ 52 ∧ (z = (m : Rat) * (2 : Rat) ^ (-1074 : Int) ∨
      z = -((m : Rat) * (2 : Rat) ^ (-1074 : Int))) := by
  have hf : bits % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  dsimp only [decodeFinite] at h
  split_ifs at h with hw hb hs
  · exact Or.inr ⟨bits % 2 ^ 52, hf, Or.inl (Option.some.inj h).symm⟩
  · exact Or.inr ⟨bits % 2 ^ 52, hf, Or.inr (Option.some.inj h).symm⟩
  · exact Or.inl h

lemma accepted_finite_nearest {x y z : Rat} {bits other : Nat} {e : Int}
    (h : Binary64Normal.acceptedPositive x bits e = true)
    (hy : Binary64Normal.decode bits = some y) (hz : decodeFinite other = some z) :
    |y - x| ≤ |z - x| := by
  obtain hn | ⟨m, hm, hp | hn⟩ := finite_classes hz
  · exact Binary64WordNearest.accepted_normal_nearest h hy hn
  · rw [hp]
    exact accepted_subnormal_nearest h hy m hm
  · have hdom := h
    simp only [Binary64Normal.acceptedPositive, decide_eq_true_eq] at hdom
    have hx : (0 : Rat) < x := lt_of_lt_of_le (zpow_pos (by norm_num) _) hdom.1
    have hz0 : z ≤ 0 := by
      rw [hn]
      have hp : (0 : Rat) ≤ 2 ^ (-1074 : Int) := le_of_lt (zpow_pos (by norm_num) _)
      exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg m) hp)
    have hc := Binary64Normal.acceptedPositive_decode h
    rw [hy] at hc
    rw [Option.some.inj hc]
    have hs : (0 : Rat) < 2 ^ (e - 52) := zpow_pos (by norm_num) _
    have he := RatRounding.quantize_nearest hs x (0 : Int)
    calc
      _ ≤ |0 - x| := by simpa using he
      _ ≤ |z - x| := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith

end Rhone.Computation.Binary64FiniteNearest
