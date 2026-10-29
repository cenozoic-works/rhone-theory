/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Rhone.Statistics.AtomicRank.CoefficientRigidity

/-! # Exact power-sum polynomials and leading coefficients for the grid argument -/

@[expose] public section

noncomputable section
open Polynomial
namespace Rhone.Statistics.AtomicRank

def powerSumQ (q : ℕ) : ℚ[X] :=
  C (((q : ℚ) + 1)⁻¹) * (Polynomial.bernoulli (q + 1) - C (_root_.bernoulli (q + 1))) -
    C ((0 : ℚ) ^ q)

def powerSum (q : ℕ) : ℝ[X] := (powerSumQ q).map (algebraMap ℚ ℝ)

lemma powerSumQ_eval_nat (q m : ℕ) :
    (powerSumQ q).eval (m : ℚ) = (∑ j ∈ Finset.range m, (j : ℚ) ^ q) - (0 : ℚ) ^ q := by
  simp only [powerSumQ, eval_sub, eval_mul, eval_C]
  rw [Polynomial.bernoulli_succ_eval]
  have hd : (q : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma powerSumQ_coeff_top (q : ℕ) :
    (powerSumQ q).coeff (q + 1) = ((q : ℚ) + 1)⁻¹ := by
  simp only [powerSumQ, coeff_sub, coeff_C_mul, coeff_C, coeff_bernoulli]
  simp

lemma powerSumQ_coeff_above {q i : ℕ} (hi : q + 1 < i) : (powerSumQ q).coeff i = 0 := by
  have hi0 : i ≠ 0 := by omega
  simp only [powerSumQ, coeff_sub, coeff_C_mul, coeff_C, coeff_bernoulli]
  simp [not_le.mpr hi, hi0]

lemma powerSumQ_degree_le (q : ℕ) : (powerSumQ q).natDegree ≤ q + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  exact powerSumQ_coeff_above hi

lemma powerSum_coeff_top (q : ℕ) :
    (powerSum q).coeff (q + 1) = ((q : ℝ) + 1)⁻¹ := by
  simp [powerSum, powerSumQ_coeff_top]

lemma powerSum_coeff_above {q i : ℕ} (hi : q + 1 < i) : (powerSum q).coeff i = 0 := by
  simp [powerSum, powerSumQ_coeff_above hi]

lemma powerSum_degree_le (q : ℕ) : (powerSum q).natDegree ≤ q + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  exact powerSum_coeff_above hi

lemma powerSum_eval_nat (q m : ℕ) :
    (powerSum q).eval (m : ℝ) = (∑ j ∈ Finset.range m, (j : ℝ) ^ q) - (0 : ℝ) ^ q := by
  have he := Polynomial.eval_map_apply (p := powerSumQ q) (f := algebraMap ℚ ℝ) (m : ℚ)
  simpa [powerSum, powerSumQ_eval_nat] using he

lemma powerSum_zero : powerSum 0 = X - 1 := by
  simp [powerSum, powerSumQ, div_eq_mul_inv]

end Rhone.Statistics.AtomicRank
