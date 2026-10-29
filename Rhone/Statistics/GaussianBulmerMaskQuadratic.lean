/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.GaussianBulmerMasks
public import Mathlib.Probability.Moments.Variance
/-!
# Quadratic fluctuations under the independent fair Mendelian locus-mask law

Source: bulmer1974, p. 282; turelli2017_infinitesimal, §4, p. 48. -/
@[expose] public section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory Probability.DiploidMarginalSelection
open Finset
def maskQuadratic (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → Fin 2) : ℝ :=
  ∑ i, ∑ j, G i j * maskSign b i * maskSign b j
theorem maskQuadratic_mean (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ) :
    (∫ b, maskQuadratic n G b ∂meiosisMaskLaw n) = Matrix.trace G := by
  unfold maskQuadratic Matrix.trace
  simp_rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [mul_assoc, integral_const_mul, maskSign_product]
  simp
theorem maskSign_four_offDiagonal (n : ℕ) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) :
    (∫ b, (maskSign b i * maskSign b j) *
      (maskSign b k * maskSign b l) ∂meiosisMaskLaw n) =
      if (i = k ∧ j = l) ∨ (i = l ∧ j = k) then 1 else 0 := by
  have hs (b : Fin n → Fin 2) (a : Fin n) : maskSign b a ^ 2 = 1 := by
    unfold maskSign
    split <;> norm_num
  by_cases hik : i = k
  · subst k
    have heq : (fun b : Fin n → Fin 2 => (maskSign b i * maskSign b j) *
        (maskSign b i * maskSign b l)) = fun b => maskSign b j * maskSign b l := by
      funext b
      calc
        _ = maskSign b i ^ 2 * (maskSign b j * maskSign b l) := by ring
        _ = _ := by rw [hs]; ring
    rw [heq, maskSign_product]
    simp [Ne.symm hij]
  by_cases hil : i = l
  · subst l
    have heq : (fun b : Fin n → Fin 2 => (maskSign b i * maskSign b j) *
        (maskSign b k * maskSign b i)) = fun b => maskSign b j * maskSign b k := by
      funext b
      calc
        _ = maskSign b i ^ 2 * (maskSign b j * maskSign b k) := by ring
        _ = _ := by rw [hs]; ring
    rw [heq, maskSign_product]
    simp [hik]
  by_cases hjk : j = k
  · subst k
    have heq : (fun b : Fin n → Fin 2 => (maskSign b i * maskSign b j) *
        (maskSign b j * maskSign b l)) = fun b => maskSign b i * maskSign b l := by
      funext b
      calc
        _ = maskSign b j ^ 2 * (maskSign b i * maskSign b l) := by ring
        _ = _ := by rw [hs]; ring
    rw [heq, maskSign_product]
    simp [hil, hik]
  by_cases hjl : j = l
  · subst l
    have heq : (fun b : Fin n → Fin 2 => (maskSign b i * maskSign b j) *
        (maskSign b k * maskSign b j)) = fun b => maskSign b i * maskSign b k := by
      funext b
      calc
        _ = maskSign b j ^ 2 * (maskSign b i * maskSign b k) := by ring
        _ = _ := by rw [hs]; ring
    rw [heq, maskSign_product]
    simp [hil, hik]
  have hi : iIndepFun (fun a : Fin n => fun b : Fin n → Fin 2 => maskSign b a)
      (meiosisMaskLaw n) := iIndepFun_pi (fun _ => (measurable_of_countable
        (fun c : Fin 2 => if c = 0 then (1 : ℝ) else -1)).aemeasurable)
  have hp := (hi.indepFun_prodMk_prodMk (fun a => by unfold maskSign; fun_prop)
    i j k l hik hil hjk hjl).comp
    (show Measurable (fun x : ℝ × ℝ => x.1 * x.2) by fun_prop)
    (show Measurable (fun x : ℝ × ℝ => x.1 * x.2) by fun_prop)
  change IndepFun (fun b => maskSign b i * maskSign b j)
    (fun b => maskSign b k * maskSign b l) (meiosisMaskLaw n) at hp
  rw [hp.integral_fun_mul_eq_mul_integral Integrable.of_finite.aestronglyMeasurable
    Integrable.of_finite.aestronglyMeasurable, maskSign_product, maskSign_product]
  simp [hij, hkl, hik, hil]
theorem maskQuadratic_variance (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.IsSymm) :
    variance (maskQuadratic n G) (meiosisMaskLaw n) =
      2 * ∑ i, ∑ j, if i = j then 0 else (G i j) ^ 2 := by
  let T (b : Fin n → Fin 2) (i j : Fin n) :=
    if i = j then (0 : ℝ) else G i j * maskSign b i * maskSign b j
  have hs (b : Fin n → Fin 2) (a : Fin n) : maskSign b a ^ 2 = 1 := by
    unfold maskSign
    split <;> norm_num
  have hc (b : Fin n → Fin 2) : maskQuadratic n G b - Matrix.trace G =
      ∑ i, ∑ j, T b i j := by
    have ht (i j : Fin n) : T b i j = G i j * maskSign b i * maskSign b j -
        (if i = j then G i i else 0) := by
      dsimp only [T]
      by_cases hij : i = j
      · subst j
        rw [ite_eq_left rfl, ite_eq_left rfl]
        rw [mul_assoc, ← pow_two, hs]
        ring
      · simp [hij]
    simp_rw [ht, sum_sub_distrib]
    simp [maskQuadratic, Matrix.trace]
  have ht (i j k l : Fin n) :
      (∫ b, T b i j * T b k l ∂meiosisMaskLaw n) =
      if i = j then 0 else
        (if k = i ∧ l = j then G i j * G k l else 0) +
        (if k = j ∧ l = i then G i j * G k l else 0) := by
    by_cases hij : i = j
    · simp [T, hij]
    by_cases hkl : k = l
    · subst l
      simp only [T, ite_eq_right hij, ite_eq_left rfl, mul_zero, integral_zero]
      split_ifs <;> simp_all
      all_goals aesop
    have heq : (fun b : Fin n → Fin 2 => T b i j * T b k l) =
        fun b => (G i j * G k l) *
          ((maskSign b i * maskSign b j) * (maskSign b k * maskSign b l)) := by
      funext b
      dsimp only [T]
      rw [ite_eq_right hij, ite_eq_right hkl]
      ring
    rw [heq, integral_const_mul, maskSign_four_offDiagonal n i j k l hij hkl]
    split_ifs <;> simp_all
    all_goals aesop
  rw [variance_eq_integral (show AEMeasurable (maskQuadratic n G) (meiosisMaskLaw n)
    from (measurable_of_countable _).aemeasurable), maskQuadratic_mean]
  simp_rw [hc, pow_two, sum_mul, mul_sum,
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [ht]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · simp [hij]
  · simp only [ite_eq_right hij, sum_add_distrib, ite_and]
    simp only [sum_ite_irrel, sum_ite_eq', mem_univ, ite_eq_left, sum_const_zero]
    have hsym : G j i = G i j := congrFun (congrFun hG i) j
    rw [hsym]
    ring
end Rhone.Statistics.GaussianBulmer
