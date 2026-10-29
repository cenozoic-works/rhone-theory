/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.PowerSum
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Roots

/-! # Scaled power sums and exact interpolation on a finite equally spaced grid -/

@[expose] public section

noncomputable section
open Polynomial
namespace Rhone.Statistics.AtomicRank

def scaledPowerSum (h : ℝ) (q : ℕ) : ℝ[X] :=
  C (h ^ (q + 1)) * (powerSum q).comp (C h⁻¹ * X)

lemma scaledPowerSum_coeff (h : ℝ) (q i : ℕ) :
    (scaledPowerSum h q).coeff i = h ^ (q + 1) * ((powerSum q).coeff i * h⁻¹ ^ i) := by
  rw [scaledPowerSum, coeff_C_mul, comp_C_mul_X_coeff]

lemma scaledPowerSum_coeff_top {h : ℝ} (hh : h ≠ 0) (q : ℕ) :
    (scaledPowerSum h q).coeff (q + 1) = ((q : ℝ) + 1)⁻¹ := by
  rw [scaledPowerSum_coeff, powerSum_coeff_top]
  calc
    _ = ((q : ℝ) + 1)⁻¹ * (h ^ (q + 1) * h⁻¹ ^ (q + 1)) := by ring
    _ = _ := by rw [← mul_pow, mul_inv_cancel₀ hh, one_pow, mul_one]

lemma scaledPowerSum_coeff_above (h : ℝ) {q i : ℕ} (hi : q + 1 < i) :
    (scaledPowerSum h q).coeff i = 0 := by
  rw [scaledPowerSum_coeff, powerSum_coeff_above hi, zero_mul, mul_zero]

lemma scaledPowerSum_degree_le (h : ℝ) (q : ℕ) :
    (scaledPowerSum h q).natDegree ≤ q + 1 := by
  exact natDegree_le_iff_coeff_eq_zero.mpr fun i hi => scaledPowerSum_coeff_above h hi

lemma scaledPowerSum_eval_grid {h : ℝ} (hh : h ≠ 0) (q m : ℕ) :
    (scaledPowerSum h q).eval ((m : ℝ) * h) =
      h ^ (q + 1) * ((∑ j ∈ Finset.range m, (j : ℝ) ^ q) - (0 : ℝ) ^ q) := by
  simp only [scaledPowerSum, eval_mul, eval_C, eval_comp, eval_X]
  have he : h⁻¹ * ((m : ℝ) * h) = m := by field_simp
  rw [he, powerSum_eval_nat]

lemma scaledPowerSum_eval_succ_grid {h : ℝ} (hh : h ≠ 0) (q m : ℕ) :
    (scaledPowerSum h q).eval (((m + 1 : ℕ) : ℝ) * h) =
      h * ∑ j ∈ Finset.range m, ((((j + 1 : ℕ) : ℝ) * h) ^ q) := by
  rw [scaledPowerSum_eval_grid hh, Finset.sum_range_succ', Nat.cast_zero, add_sub_cancel_right]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow, pow_succ]
  ring

lemma positive_grid_injective (n : ℕ) {h : ℝ} (hh : h ≠ 0) :
    Function.Injective (fun i : Fin (n + 1) => ((i.val : ℝ) + 1) * h) := by
  intro i j he
  have hs := mul_right_cancel₀ hh he
  have hv : (i.val : ℝ) = j.val := add_right_cancel hs
  exact Fin.ext (by exact_mod_cast hv)

theorem polynomial_eq_zero_of_grid (n : ℕ) {h : ℝ} (hh : h ≠ 0) (p : ℝ[X])
    (hd : p.natDegree ≤ n)
    (he : ∀ i : Fin (n + 1), p.eval (((i.val : ℝ) + 1) * h) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (positive_grid_injective n hh) he
  simpa using Nat.lt_succ_of_le hd

end Rhone.Statistics.AtomicRank
