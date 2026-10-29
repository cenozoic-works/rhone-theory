/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Algebraic elimination for the three-event panmictic invariant -/

@[expose] public section

namespace Rhone.Statistics.Identifiability.ThreeSampleRootFree

def polynomial (a b z : ℝ) : ℝ :=
  (z ^ 3 + b * (a ^ 2 - 1)) ^ 3 + 27 * a ^ 2 * b ^ 2 * z ^ 3

lemma polynomial_cube_identity (x y z : ℝ) :
    polynomial (x ^ 3) (y ^ 3) z =
      (z ^ 3 + y ^ 3 * (x ^ 6 - 1)) ^ 3 + (3 * x ^ 2 * y ^ 2 * z) ^ 3 := by
  unfold polynomial
  ring

lemma polynomial_zero_iff (x y z : ℝ) (hy : 0 ≤ y) :
    polynomial (x ^ 3) (y ^ 3) z = 0 ↔ z = y * (1 - x ^ 2) := by
  rw [polynomial_cube_identity]
  have hc : ∀ d r : ℝ, d ^ 3 + r ^ 3 = 0 ↔ d + r = 0 := by
    intro d r
    have hi := (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow_inj (a := d) (b := -r)
    constructor
    · intro h
      have he : d ^ 3 = (-r) ^ 3 := by nlinarith only [h]
      linarith only [hi.mp he]
    · intro h
      have he : d = -r := by linarith only [h]
      rw [he]
      ring
  rw [hc]
  let v := y * (1 - x ^ 2)
  let q := z ^ 2 + z * v + v ^ 2 + 3 * x ^ 2 * y ^ 2
  have hf : z ^ 3 + y ^ 3 * (x ^ 6 - 1) + 3 * x ^ 2 * y ^ 2 * z =
      (z - v) * q := by dsimp [v, q]; ring
  rw [hf]
  by_cases hzero : y = 0
  · subst y
    simp [v, q]
  · have hpos : 0 < y := lt_of_le_of_ne hy (Ne.symm hzero)
    have hsq : 0 < 3 * y ^ 2 * (1 + x ^ 2) ^ 2 := by positivity
    have hq : 0 < q := by
      have hid : 4 * q = (2 * z + v) ^ 2 + 3 * y ^ 2 * (1 + x ^ 2) ^ 2 := by
        dsimp [q, v]
        ring
      nlinarith only [hid, hsq, sq_nonneg (2 * z + v)]
    rw [mul_eq_zero]
    simp only [ne_of_gt hq, or_false, sub_eq_zero]
    rfl

theorem polynomial_zero_iff_rpow (a b z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    polynomial a b z = 0 ↔ z = b ^ (1 / 3 : ℝ) * (1 - (a ^ (1 / 3 : ℝ)) ^ 2) := by
  have cube (v : ℝ) (hv : 0 ≤ v) : (v ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = v := by
    rw [← Real.rpow_mul_natCast hv]
    norm_num
  have h := polynomial_zero_iff (a ^ (1 / 3 : ℝ)) (b ^ (1 / 3 : ℝ)) z
    (Real.rpow_nonneg hb _)
  rwa [cube a ha, cube b hb] at h

noncomputable def eventPolynomial (a b c : ℝ) : ℝ := polynomial a b ((2 / 3 : ℝ) * c)

theorem eventPolynomial_zero_iff (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    eventPolynomial a b c = 0 ↔
      c = (3 / 2 : ℝ) * b ^ (1 / 3 : ℝ) * (1 - (a ^ (1 / 3 : ℝ)) ^ 2) := by
  unfold eventPolynomial
  rw [polynomial_zero_iff_rpow a b _ ha hb]
  constructor <;> intro h <;> nlinarith only [h]

end Rhone.Statistics.Identifiability.ThreeSampleRootFree
