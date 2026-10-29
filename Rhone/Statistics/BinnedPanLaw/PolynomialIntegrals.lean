/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.Primitive

/-! # Finite polynomial quadrature identities for histogram moments -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.BinnedPanLaw

def polynomialIntegral {d : ℕ} (c : Fin d → ℝ) (e : Fin d → ℕ) (a b : ℝ) : ℝ :=
  ∑ i, c i * powerIntegral (e i) a b

theorem polynomial_integral {d : ℕ} (c : Fin d → ℝ) (e : Fin d → ℕ) (a b : ℝ) :
    (∫ x in a..b, ∑ i, c i * x ^ e i) = polynomialIntegral c e a b := by
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, power_integral, polynomialIntegral]
  · intro i _
    exact (show Continuous (fun x : ℝ => c i * x ^ e i) by fun_prop).intervalIntegrable _ _

def cubeIntegral (p : ℕ) (A B a b : ℝ) : ℝ :=
  polynomialIntegral ![A ^ 3, 3 * A ^ 2 * B, 3 * A * B ^ 2, B ^ 3]
    ![p, p + 1, p + 2, p + 3] a b

theorem cube_integral (p : ℕ) (A B a b : ℝ) :
    (∫ x in a..b, x ^ p * (A + B * x) ^ 3) = cubeIntegral p A B a b := by
  rw [cubeIntegral, ← polynomial_integral]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, pow_add]
  ring

def crossIntegral (p q : ℕ) (A B C a b : ℝ) : ℝ :=
  polynomialIntegral
    ![C * A ^ 2, 2 * C * A * B, C * B ^ 2,
      A ^ 3 / (q + 1), 2 * A ^ 2 * B / (q + 1), A * B ^ 2 / (q + 1),
      A ^ 2 * B / (q + 2), 2 * A * B ^ 2 / (q + 2), B ^ 3 / (q + 2)]
    ![p, p + 1, p + 2, p + q + 1, p + q + 2, p + q + 3,
      p + q + 2, p + q + 3, p + q + 4] a b

theorem cross_integral (p q : ℕ) (A B C a b : ℝ) :
    (∫ x in a..b, x ^ p * (A + B * x) ^ 2 *
      (C + A / (q + 1) * x ^ (q + 1) + B / (q + 2) * x ^ (q + 2))) =
        crossIntegral p q A B C a b := by
  rw [crossIntegral, ← polynomial_integral]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, pow_add]
  ring

end Rhone.Statistics.BinnedPanLaw
