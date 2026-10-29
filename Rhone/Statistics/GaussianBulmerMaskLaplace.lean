/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.GaussianBulmerMaskQuadratic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Matrix.PosDef
/-!
# Bound the Mendelian quadratic Laplace fluctuation by its derived variance

Source: bulmer1974, p. 282; turelli2017_infinitesimal, §4, p. 48. -/
@[expose] public section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory Probability.DiploidMarginalSelection
open Finset Set
theorem exp_neg_taylor_bound (a x y : ℝ) (ha : 0 ≤ a)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-a * x) - Real.exp (-a * y) +
      a * Real.exp (-a * y) * (x - y)| ≤ a ^ 2 / 2 * (x - y) ^ 2 := by
  by_cases hxy : y = x
  · subst x
    simp
  let f : ℝ → ℝ := fun z => Real.exp (-a * z)
  have hf : ContDiff ℝ 2 f := by dsimp [f]; fun_prop
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (n := 1) hxy hf.contDiffOn
  have hpoly : taylorWithinEval f 1 (uIcc y x) y x =
      Real.exp (-a * y) - a * Real.exp (-a * y) * (x - y) := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      (by dsimp [f]; fun_prop) (left_mem_uIcc), iteratedDeriv_exp_const_mul]
    simp [f]
    ring
  have hzpos : 0 ≤ z := (le_min hy hx).trans hz.1.le
  have hexp : Real.exp (-a * z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hzrem : Real.exp (-a * x) - Real.exp (-a * y) +
      a * Real.exp (-a * y) * (x - y) =
      a ^ 2 * Real.exp (-a * z) * (x - y) ^ 2 / 2 := by
    rw [hpoly] at he
    dsimp only [f] at he
    rw [iteratedDeriv_exp_const_mul] at he
    norm_num at he
    simp only [neg_mul] at he ⊢
    linarith
  rw [hzrem, abs_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left hexp (sq_nonneg a)
  have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg (x-y))
  nlinarith
theorem maskQuadratic_laplace_fluctuation (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (t : ℝ) :
    |(∫ b, Real.exp (-(t ^ 2 / 8) * maskQuadratic n G b) ∂meiosisMaskLaw n) -
      Real.exp (-(t ^ 2 / 8) * Matrix.trace G)| ≤
      (t ^ 4 / 64) * ∑ i, ∑ j, if i = j then 0 else (G i j) ^ 2 := by
  let a : ℝ := t ^ 2 / 8
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hQ (b : Fin n → Fin 2) : 0 ≤ maskQuadratic n G b := by
    have hp := hG.dotProduct_mulVec_nonneg (fun i => maskSign b i)
    simpa [maskQuadratic, dotProduct, Matrix.mulVec, mul_sum,
      mul_comm, mul_left_comm, mul_assoc] using hp
  have htr : 0 ≤ Matrix.trace G := hG.trace_nonneg
  have hsym : G.IsSymm := Matrix.isHermitian_iff_isSymm.mp hG.1
  let R (b : Fin n → Fin 2) := Real.exp (-a * maskQuadratic n G b) -
    Real.exp (-a * Matrix.trace G) +
    a * Real.exp (-a * Matrix.trace G) * (maskQuadratic n G b - Matrix.trace G)
  have hR : (∫ b, R b ∂meiosisMaskLaw n) =
      (∫ b, Real.exp (-a * maskQuadratic n G b) ∂meiosisMaskLaw n) -
      Real.exp (-a * Matrix.trace G) := by
    dsimp only [R]
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
      integral_sub Integrable.of_finite Integrable.of_finite, maskQuadratic_mean]
    simp
  change |(∫ b, Real.exp (-a * maskQuadratic n G b) ∂meiosisMaskLaw n) -
    Real.exp (-a * Matrix.trace G)| ≤ _
  rw [← hR]
  calc
    |∫ b, R b ∂meiosisMaskLaw n| ≤ ∫ b, |R b| ∂meiosisMaskLaw n :=
      abs_integral_le_integral_abs
    _ ≤ ∫ b, a ^ 2 / 2 * (maskQuadratic n G b - Matrix.trace G) ^ 2 ∂meiosisMaskLaw n := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro b
      exact exp_neg_taylor_bound a _ _ ha (hQ b) htr
    _ = (a ^ 2 / 2) * variance (maskQuadratic n G) (meiosisMaskLaw n) := by
      rw [integral_const_mul, variance_eq_integral
        (measurable_of_countable _).aemeasurable, maskQuadratic_mean]
    _ = _ := by
      rw [maskQuadratic_variance n G hsym]
      dsimp only [a]
      ring
end Rhone.Statistics.GaussianBulmer
