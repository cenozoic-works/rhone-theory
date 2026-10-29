/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.MoranAbsorption
public import Rhone.MarkovChain.MoranConditional

/-!
# Neutral Moran absorption and conditional fixation times in closed form

Source: ewens2004, sec. 3.4. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

/-- Source: ewens2004, sec. 3.4. -/
theorem moranGeomSum_one (k : ℕ) : moranGeomSum 1 k = (k : ℝ) := by
  simp [moranGeomSum]

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_one (N : ℕ) :
    moranAbsorptionTime N 1 = (N : ℝ) * ∑ j ∈ Icc 1 (N - 1), 1 / (j : ℝ) := by
  have he : Icc 1 (1 - 1) = (∅ : Finset ℕ) := Icc_eq_empty_of_lt (by norm_num)
  rw [moranAbsorptionTime, he, sum_empty, mul_zero, zero_add, Nat.cast_one, one_mul]

/-- Source: ewens2004, sec. 3.4. -/
theorem moranSelectionGreen_neutral_le {N i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j < N) :
    moranSelectionGreen N 1 i j = (N : ℝ) * i / j := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNj : (N : ℝ) - j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : N ≠ j))
  rw [moranSelectionGreen, min_eq_left hij, max_eq_right hij, moranFixProb_one,
    moranGeomSum_one, moranGeomSum_one, moranUp_one, inv_one, one_pow, mul_one]
  field_simp

/-- Source: ewens2004, sec. 3.4. -/
theorem moranSelectionGreen_neutral_ge {N i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i) (hi : i < N) :
    moranSelectionGreen N 1 i j = (N : ℝ) * ((N : ℝ) - i) / ((N : ℝ) - j) := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNj : (N : ℝ) - j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : N ≠ j))
  rw [moranSelectionGreen, min_eq_right hji, max_eq_left hji, moranFixProb_one,
    moranGeomSum_one, moranGeomSum_one, moranUp_one, inv_one, one_pow, mul_one]
  field_simp

/-- Source: ewens2004, sec. 3.4. -/
theorem moranConditionalFixationTime_neutral {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) :
    moranConditionalFixationTime N 1 i =
      (N : ℝ) * ((N : ℝ) - i) * (1 + (∑ j ∈ Icc 1 (i - 1), (j : ℝ) / ((N : ℝ) - j)) / i) := by
  have hi0 : (i : ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rcases hiN.eq_or_lt with rfl | hlt
  · have hz : ∀ j ∈ Icc 1 (i - 1), moranSelectionGreen i 1 i j * moranFixProb i 1 j = 0 := by
      intro j hj
      have hji : j ≤ i := by have := mem_Icc.mp hj; omega
      rw [moranSelectionGreen, max_eq_left hji, sub_self, mul_zero, zero_div, zero_mul]
    rw [moranConditionalFixationTime, sum_eq_zero hz, zero_div, sub_self, mul_zero, zero_mul]
  · have hu : Icc 1 (N - 1) = Icc 1 (i - 1) ∪ Icc i (N - 1) := by
      ext j
      simp only [mem_Icc, mem_union]
      omega
    have hd : Disjoint (Icc 1 (i - 1)) (Icc i (N - 1)) := by
      apply disjoint_left.mpr
      intro j hj hk
      simp only [mem_Icc] at hj hk
      omega
    have hlow : ∑ j ∈ Icc 1 (i - 1), moranSelectionGreen N 1 i j * moranFixProb N 1 j =
        ((N : ℝ) - i) * ∑ j ∈ Icc 1 (i - 1), (j : ℝ) / ((N : ℝ) - j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hj' := mem_Icc.mp hj
      have hNj : (N : ℝ) - j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : N ≠ j))
      rw [moranSelectionGreen_neutral_ge (by omega) (by omega) hlt, moranFixProb_one]
      field_simp
    have hhigh : ∑ j ∈ Icc i (N - 1), moranSelectionGreen N 1 i j * moranFixProb N 1 j =
        ((N : ℝ) - i) * i := by
      have hterm : ∀ j ∈ Icc i (N - 1),
          moranSelectionGreen N 1 i j * moranFixProb N 1 j = (i : ℝ) := by
        intro j hj
        have hj' := mem_Icc.mp hj
        have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
        rw [moranSelectionGreen_neutral_le hi (by omega) (by omega), moranFixProb_one]
        field_simp
      have hcard : N - 1 + 1 - i = N - i := by omega
      rw [sum_congr rfl hterm, sum_const, Nat.card_Icc, nsmul_eq_mul, hcard,
        Nat.cast_sub hlt.le]
    rw [moranConditionalFixationTime, hu, sum_union hd, hlow, hhigh, moranFixProb_one]
    field_simp
    ring

/-- Source: ewens2004, sec. 3.4. -/
theorem moranConditionalFixationTime_neutral_one {N : ℕ} (hN : 1 ≤ N) :
    moranConditionalFixationTime N 1 1 = (N : ℝ) * ((N : ℝ) - 1) := by
  have he : Icc 1 (1 - 1) = (∅ : Finset ℕ) := Icc_eq_empty_of_lt (by norm_num)
  rw [moranConditionalFixationTime_neutral le_rfl hN, he, sum_empty, zero_div, add_zero,
    mul_one, Nat.cast_one]

end Rhone.MarkovChain
