/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.GridPolynomials

/-! # The highest-degree coefficients of the exact grid jump operator -/

@[expose] public section

noncomputable section
open Polynomial
namespace Rhone.Statistics.AtomicRank

def jumpBasis (h z : ℝ) (p q : ℕ) : ℝ[X] :=
  C ((p : ℝ) * z ^ (p - 1)) * (scaledPowerSum h q + X ^ (q + 1)) -
    C ((q : ℝ) * z ^ (q - 1)) * (X ^ (p + 1) - C (h / 2) * X ^ p)

def jumpCoefficientBasis (h : ℝ) (v p q : ℕ) : ℝ[X] :=
  C ((p : ℝ) * ((scaledPowerSum h q).coeff v + (if q + 1 = v then 1 else 0))) *
      X ^ (p - 1) -
    C ((q : ℝ) * ((if p + 1 = v then 1 else 0) - (h / 2) * (if p = v then 1 else 0))) *
      X ^ (q - 1)

lemma jumpBasis_coeff (h z : ℝ) (v p q : ℕ) :
    (jumpBasis h z p q).coeff v = (jumpCoefficientBasis h v p q).eval z := by
  simp only [jumpBasis, jumpCoefficientBasis, coeff_sub, coeff_C_mul, coeff_add, coeff_X_pow,
    eval_sub, eval_mul, eval_C, eval_pow, eval_X, eq_comm]
  ring

lemma inverse_add_one_eq_growth (q : ℕ) : ((q : ℝ) + 1)⁻¹ + 1 = growth q := by
  unfold growth
  have hd : (q : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma leading_first {h : ℝ} (hh : h ≠ 0) {p q p' q' : ℕ}
    (hp : 0 < p) (hd : p' + q' ≤ p + q) :
    (C ((p' : ℝ) * ((scaledPowerSum h q').coeff (q + 1) +
      (if q' + 1 = q + 1 then 1 else 0))) * X ^ (p' - 1)).coeff (p - 1) =
      if p' = p ∧ q' = q then (p : ℝ) * growth q else 0 := by
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hp0 : p' = 0
  · subst p'
    simp [hp.ne]
  by_cases he : p' = p
  · subst p'
    have hq : q' ≤ q := by omega
    by_cases hqe : q' = q
    · subst q'
      simp [scaledPowerSum_coeff_top hh, inverse_add_one_eq_growth]
    · have hlt : q' + 1 < q + 1 := by omega
      have hne : q' + 1 ≠ q + 1 := by omega
      simp [scaledPowerSum_coeff_above h hlt, hqe]
  · have hpred : p - 1 ≠ p' - 1 := by omega
    simp [hpred, he]

lemma leading_second (h : ℝ) {p q p' q' : ℕ}
    (hp : 0 < p) (hd : p' + q' ≤ p + q) :
    (C ((q' : ℝ) * ((if p' + 1 = q + 1 then 1 else 0) -
      (h / 2) * (if p' = q + 1 then 1 else 0))) * X ^ (q' - 1)).coeff (p - 1) =
      if p' = q ∧ q' = p then (p : ℝ) else 0 := by
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hq0 : q' = 0
  · subst q'
    simp [hp.ne]
  by_cases he : q' = p
  · subst q'
    have hpp : p' ≤ q := by omega
    have hne : p' ≠ q + 1 := by omega
    by_cases hpe : p' = q
    · subst p'
      simp
    · have hn : p' + 1 ≠ q + 1 := by omega
      simp [hpe, hne]
  · have hpred : p - 1 ≠ q' - 1 := by omega
    simp [hpred, he]

theorem jumpCoefficientBasis_top {h : ℝ} (hh : h ≠ 0) {p q p' q' : ℕ}
    (hp : 0 < p) (hd : p' + q' ≤ p + q) :
    (jumpCoefficientBasis h (q + 1) p' q').coeff (p - 1) =
      (if p' = p ∧ q' = q then (p : ℝ) * growth q else 0) -
        (if p' = q ∧ q' = p then (p : ℝ) else 0) := by
  rw [jumpCoefficientBasis, coeff_sub, leading_first hh hp hd, leading_second h hp hd]

end Rhone.Statistics.AtomicRank
