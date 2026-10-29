/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.Binary64Normal
public import Rhone.Computation.Binary64Nearest
/-! # Nearest comparison against every decoded normal binary64 word -/

@[expose] public section
namespace Rhone.Computation.Binary64WordNearest

lemma decoded_normal {bits : Nat} {y : Rat} (h : Binary64Normal.decode bits = some y) :
    ∃ (m : Nat) (d : Int), 2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧
      (y = (m : Rat) * (2 : Rat) ^ (d - 52) ∨
        y = -((m : Rat) * (2 : Rat) ^ (d - 52))) := by
  have hf : bits % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  dsimp only [Binary64Normal.decode] at h
  split_ifs at h with hv hs
  · refine ⟨2 ^ 52 + bits % 2 ^ 52, (bits / 2 ^ 52 % 2048 : Nat) - 1023,
      by omega, by norm_num at *; omega, Or.inl ?_⟩
    have he := (Option.some.inj h).symm
    have heq : ((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1023 - 52 =
        ((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1075 := by omega
    rw [heq]
    exact he
  · refine ⟨2 ^ 52 + bits % 2 ^ 52, (bits / 2 ^ 52 % 2048 : Nat) - 1023,
      by omega, by norm_num at *; omega, Or.inr ?_⟩
    have he := (Option.some.inj h).symm
    have heq : ((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1023 - 52 =
        ((bits / 2 ^ 52 % 2048 : Nat) : Int) - 1075 := by omega
    rw [heq]
    exact he

lemma accepted_normal_nearest {x y z : Rat} {e : Int} {bits other : Nat}
    (h : Binary64Normal.acceptedPositive x bits e = true)
    (hy : Binary64Normal.decode bits = some y)
    (hz : Binary64Normal.decode other = some z) :
    |y - x| ≤ |z - x| := by
  have hd := Binary64Normal.acceptedPositive_decode h
  rw [hy] at hd
  rw [Option.some.inj hd]
  simp only [Binary64Normal.acceptedPositive, decide_eq_true_eq] at h
  obtain ⟨m, d, hmlo, hmhi, hzpos | hzneg⟩ := decoded_normal hz
  · rw [hzpos]
    exact Binary64Nearest.all_binades_nearest h.1 h.2.1 d m hmlo hmhi
  · have hx : (0 : Rat) < x := lt_of_lt_of_le (zpow_pos (by norm_num) _) h.1
    have hz0 : z ≤ 0 := by
      rw [hzneg]
      have hp : (0 : Rat) ≤ 2 ^ (d - 52) := le_of_lt (zpow_pos (by norm_num) _)
      exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg m) hp)
    have hs : (0 : Rat) < 2 ^ (e - 52) := zpow_pos (by norm_num) _
    have he := RatRounding.quantize_nearest hs x (0 : Int)
    calc
      _ ≤ |0 - x| := by simpa using he
      _ ≤ |z - x| := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith

end Rhone.Computation.Binary64WordNearest
