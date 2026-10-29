/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib
/-! # Round-to-nearest-even and grid quantization of rationals with error bounds -/

@[expose] public section
namespace Rhone.Computation.RatRounding

def nearestEven (x : Rat) : Int :=
  let z := Int.floor x
  if x - z < 1 / 2 then z
  else if 1 / 2 < x - z then z + 1
  else if z % 2 = 0 then z else z + 1

lemma nearestEven_error (x : Rat) : |(nearestEven x : Rat) - x| ≤ 1 / 2 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  dsimp only [nearestEven]
  split_ifs <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith

lemma nearestEven_tie (x : Rat) (h : x - (Int.floor x : Rat) = 1 / 2) :
    nearestEven x % 2 = 0 := by
  unfold nearestEven
  simp only [h, lt_self_iff_false, ↓reduceIte]
  split_ifs with he
  · exact he
  · omega

def quantize (step x : Rat) : Rat := step * nearestEven (x / step)

lemma quantize_error {step : Rat} (hs : 0 < step) (x : Rat) :
    |quantize step x - x| ≤ step / 2 := by
  have h := nearestEven_error (x / step)
  have heq : quantize step x - x = step * ((nearestEven (x / step) : Rat) - x / step) := by
    unfold quantize
    field_simp
  rw [heq, abs_mul, abs_of_pos hs]
  calc
    step * |(nearestEven (x / step) : Rat) - x / step| ≤ step * (1 / 2) :=
      mul_le_mul_of_nonneg_left h hs.le
    _ = step / 2 := by ring

lemma quantize_relative {step x : Rat} (hs : 0 < step) (hx : 0 < x)
    (hscale : step ≤ x * (1 / (2 : Rat) ^ 52)) :
    |quantize step x - x| / x ≤ 1 / (2 : Rat) ^ 53 := by
  apply (div_le_iff₀ hx).mpr
  calc
    |quantize step x - x| ≤ step / 2 := quantize_error hs x
    _ ≤ (x * (1 / (2 : Rat) ^ 52)) / 2 := div_le_div_of_nonneg_right hscale (by norm_num)
    _ = 1 / (2 : Rat) ^ 53 * x := by ring

lemma quantize_nearest {step : Rat} (hs : 0 < step) (x : Rat) (k : Int) :
    |quantize step x - x| ≤ |step * k - x| := by
  have hl := Int.floor_le (x / step)
  have hu := Int.lt_floor_add_one (x / step)
  have hk : k ≤ Int.floor (x / step) ∨ Int.floor (x / step) + 1 ≤ k := by omega
  have hk' : (k : Rat) ≤ Int.floor (x / step) ∨ (Int.floor (x / step) : Rat) + 1 ≤ k := by
    rcases hk with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have hnear : |(nearestEven (x / step) : Rat) - x / step| ≤ |(k : Rat) - x / step| := by
    dsimp only [nearestEven]
    split_ifs <;> push_cast
    all_goals rcases hk' with hk' | hk'
    all_goals first
      | rw [abs_of_nonpos (by linarith)]
        rw [abs_of_nonpos (by linarith)]
        linarith
      | rw [abs_of_nonneg (by linarith)]
        rw [abs_of_nonneg (by linarith)]
        linarith
      | rw [abs_of_nonpos (by linarith)]
        rw [abs_of_nonneg (by linarith)]
        linarith
      | rw [abs_of_nonneg (by linarith)]
        rw [abs_of_nonpos (by linarith)]
        linarith
  have hleft : quantize step x - x = step * ((nearestEven (x / step) : Rat) - x / step) := by
    unfold quantize
    field_simp
  have hright : step * k - x = step * ((k : Rat) - x / step) := by field_simp
  rw [hleft, hright, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hnear (abs_nonneg step)

end Rhone.Computation.RatRounding
