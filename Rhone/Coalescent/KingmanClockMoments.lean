/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.MarkovChain.JumpHold
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Tactic.Ring
/-!
# Second moments of the independent standard exponential clocks used by Kingman

Source: kingman1982, eq. (1.7), (1.12)–(1.13). -/
@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem lintegral_ofReal_expMeasure_one_sq :
    (∫⁻ t, (ENNReal.ofReal t)^2 ∂ProbabilityTheory.expMeasure 1) = 2 := by
  have hg : Real.Gamma 3 = 2 := by
    norm_num [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  have hpt : ∀ t : ℝ, gammaPDF 1 1 t * (ENNReal.ofReal t)^2 =
      2 * gammaPDF 3 1 t := by
    intro t
    rw [gammaPDF_eq, gammaPDF_eq]
    by_cases ht : 0 ≤ t
    · simp only [ht, ↓reduceIte]
      rw [← ENNReal.ofReal_pow ht, ← ENNReal.ofReal_mul (by positivity)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num [Real.Gamma_one]
      ring
    · simp [ht, ENNReal.ofReal_of_nonpos (not_le.1 ht).le]
  have hm : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hm (by fun_prop)]
  simp only [Pi.mul_apply, hpt]
  have hm3 : Measurable (gammaPDF 3 1) :=
    (measurable_gammaPDFReal 3 1).ennreal_ofReal
  rw [lintegral_const_mul _ hm3,
    lintegral_gammaPDF_eq_one (by norm_num) one_pos,
    mul_one]
theorem lintegral_clock_product (i j : ℕ) :
    (∫⁻ e, ENNReal.ofReal (e i) * ENNReal.ofReal (e j)
      ∂Rhone.MarkovChain.clockLaw) = if i = j then 2 else 1 := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true, ← pow_two]
    rw [← lintegral_ofReal_expMeasure_one_sq,
      ← Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) i,
      lintegral_map (by fun_prop) (measurable_pi_apply i)]
    rfl
  · rw [ite_eq_right hij]
    have hind : IndepFun (fun e : ℕ → ℝ => ENNReal.ofReal (e i))
        (fun e => ENNReal.ofReal (e j)) Rhone.MarkovChain.clockLaw :=
      (iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1)
        (X := fun _ => ENNReal.ofReal) (fun _ => ENNReal.measurable_ofReal)).indepFun hij
    have h := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      (by fun_prop) (by fun_prop) hind
    simpa only [Pi.mul_apply, Rhone.MarkovChain.lintegral_ofReal_clockLaw, mul_one] using h
theorem lintegral_weighted_clock_sum_sq (s : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ k ∈ s, 0 ≤ a k) :
    (∫⁻ e, (∑ k ∈ s, ENNReal.ofReal (a k) * ENNReal.ofReal (e k))^2
      ∂Rhone.MarkovChain.clockLaw) =
      ENNReal.ofReal ((∑ k ∈ s, a k)^2 + ∑ k ∈ s, (a k)^2) := by
  classical
  have hpoint : ∀ e : ℕ → ℝ,
      (∑ k ∈ s, ENNReal.ofReal (a k) * ENNReal.ofReal (e k))^2 =
      ∑ i ∈ s, ∑ j ∈ s, ENNReal.ofReal (a i * a j) *
        (ENNReal.ofReal (e i) * ENNReal.ofReal (e j)) := by
    intro e
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ENNReal.ofReal_mul (ha i hi)]
    ring
  simp_rw [hpoint]
  rw [lintegral_finsetSum s (by intro i hi; fun_prop)]
  have hrow : ∀ i ∈ s,
      (∫⁻ e, ∑ j ∈ s, ENNReal.ofReal (a i * a j) *
        (ENNReal.ofReal (e i) * ENNReal.ofReal (e j)) ∂Rhone.MarkovChain.clockLaw) =
      ENNReal.ofReal ((a i)^2 + a i * ∑ j ∈ s, a j) := by
    intro i hi
    rw [lintegral_finsetSum s (by intro j hj; fun_prop)]
    have hterms : ∀ j ∈ s, (∫⁻ e, ENNReal.ofReal (a i * a j) *
        (ENNReal.ofReal (e i) * ENNReal.ofReal (e j)) ∂Rhone.MarkovChain.clockLaw) =
        ENNReal.ofReal (a i * a j * (if i = j then 2 else 1)) := by
      intro j hj
      rw [lintegral_const_mul _ (by fun_prop), lintegral_clock_product]
      split_ifs
      · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (mul_nonneg (ha i hi) (ha j hj))]
      · simp only [mul_one]
    rw [Finset.sum_congr rfl hterms,
      ← ENNReal.ofReal_sum_of_nonneg (fun j hj =>
        mul_nonneg (mul_nonneg (ha i hi) (ha j hj)) (by split_ifs <;> norm_num))]
    congr 1
    have hterm : ∀ j, a i * a j * (if i = j then 2 else 1) =
        a i * a j + if i = j then (a i)^2 else 0 := by
      intro j
      by_cases hij : i = j
      · subst j; simp only [ite_true]; ring
      · simp [hij]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hi, add_comm]
  rw [Finset.sum_congr rfl hrow,
    ← ENNReal.ofReal_sum_of_nonneg (fun i hi =>
      add_nonneg (sq_nonneg _) (mul_nonneg (ha i hi)
        (Finset.sum_nonneg fun j hj => ha j hj)))]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← pow_two]
  exact add_comm _ _
end Rhone.Coalescent
