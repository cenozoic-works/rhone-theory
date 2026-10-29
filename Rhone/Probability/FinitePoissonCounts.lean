/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.PoissonMoments
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Finite independent Poisson mutation count moments -/

@[expose] public section
namespace Rhone.Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun k : ℕ => (k : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa [Real.norm_eq_abs, abs_of_nonneg] using (poisson_hasSum_count r).summable

theorem poisson_integrable_count_sq (r : ℝ≥0) :
    Integrable (fun k : ℕ => (k : ℝ) ^ 2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (poisson_hasSum_count_factorial_two r).add (poisson_hasSum_count r)
  have he (k : ℕ) :
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ) *
        ((k : ℝ) * ((k : ℝ) - 1)) +
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ) * (k : ℝ) =
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ) * (k : ℝ) ^ 2 := by ring
  simp_rw [he] at hs
  simpa [Real.norm_eq_abs, abs_of_nonneg] using hs.summable

theorem pi_poisson_integrable_count {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) (i : ι) :
    Integrable (fun x : ι → ℕ => (x i : ℝ)) (Measure.pi (fun j => poissonMeasure (r j))) := by
  exact (measurePreserving_eval (fun j => poissonMeasure (r j)) i).integrable_comp_of_integrable
    (poisson_integrable_count (r i))

theorem pi_poisson_integral_count {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) (i : ι) :
    ∫ x : ι → ℕ, (x i : ℝ) ∂Measure.pi (fun j => poissonMeasure (r j)) = r i := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).aestronglyMeasurable,
    (measurePreserving_eval (fun j => poissonMeasure (r j)) i).map_eq]
  exact poisson_integral_count (r i)

theorem pi_poisson_integrable_count_product {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (i j : ι) :
    Integrable (fun x : ι → ℕ => (x i : ℝ) * (x j : ℝ))
      (Measure.pi (fun k => poissonMeasure (r k))) := by
  classical
  by_cases hij : i = j
  · subst j
    have h :=
      (measurePreserving_eval (fun k => poissonMeasure (r k)) i).integrable_comp_of_integrable
       (poisson_integrable_count_sq (r i))
    simpa only [Function.comp_def, Function.eval, pow_two] using h
  · have hind : iIndepFun (fun k (x : ι → ℕ) => (x k : ℝ))
        (Measure.pi (fun k => poissonMeasure (r k))) :=
      iIndepFun_pi (fun _ => Measurable.of_discrete.aemeasurable)
    convert (hind.indepFun hij).integrable_mul
      (pi_poisson_integrable_count r i) (pi_poisson_integrable_count r j) using 1

theorem pi_poisson_integral_count_product_general {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (i j : ι) :
    ∫ x : ι → ℕ, (x i : ℝ) * (x j : ℝ)
      ∂Measure.pi (fun k => poissonMeasure (r k)) =
    @ite ℝ (i = j) (Classical.propDecidable _)
      ((r i : ℝ) ^ 2 + r i) ((r i : ℝ) * r j) := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    simp_rw [← pow_two]
    have he := integral_map (μ := Measure.pi (fun k => poissonMeasure (r k)))
      (φ := fun x : ι → ℕ => x i) (f := fun k : ℕ => (k : ℝ) ^ 2)
      (measurable_pi_apply i).aemeasurable Measurable.of_discrete.aestronglyMeasurable
    rw [(measurePreserving_eval (fun k => poissonMeasure (r k)) i).map_eq] at he
    rw [← he]
    exact poisson_integral_count_sq (r i)
  · simp only [hij, ↓reduceIte]
    have hind : iIndepFun (fun k (x : ι → ℕ) => (x k : ℝ))
        (Measure.pi (fun k => poissonMeasure (r k))) :=
      iIndepFun_pi (fun _ => Measurable.of_discrete.aemeasurable)
    have h := (hind.indepFun hij).integral_mul_eq_mul_integral
      (pi_poisson_integrable_count r i).aestronglyMeasurable
      (pi_poisson_integrable_count r j).aestronglyMeasurable
    change (∫ x : ι → ℕ, (x i : ℝ) * (x j : ℝ)
      ∂Measure.pi (fun k => poissonMeasure (r k))) = _ at h
    rw [h, pi_poisson_integral_count, pi_poisson_integral_count]

theorem pi_poisson_integral_weighted_count {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (w : ι → ℝ) :
    ∫ x : ι → ℕ, ∑ i, w i * (x i : ℝ)
      ∂Measure.pi (fun j => poissonMeasure (r j)) = ∑ i, w i * r i := by
  rw [integral_finsetSum _ (fun i _ => (pi_poisson_integrable_count r i).const_mul (w i))]
  simp_rw [integral_const_mul, pi_poisson_integral_count]

theorem pi_poisson_integral_weighted_count_sq {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (w : ι → ℝ) :
    ∫ x : ι → ℕ, (∑ i, w i * (x i : ℝ)) ^ 2
      ∂Measure.pi (fun j => poissonMeasure (r j)) =
    (∑ i, w i * r i) ^ 2 + ∑ i, w i ^ 2 * r i := by
  classical
  have hex (x : ι → ℕ) : (∑ i, w i * (x i : ℝ)) ^ 2 =
      ∑ i, ∑ j, (w i * w j) * ((x i : ℝ) * (x j : ℝ)) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hex]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (pi_poisson_integrable_count_product r i j).const_mul (w i * w j)))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    (pi_poisson_integrable_count_product r _ j).const_mul _), integral_const_mul,
    pi_poisson_integral_count_product_general]
  have hp (i j : ι) :
      (if i = j then (r i : ℝ) ^ 2 + r i else (r i : ℝ) * r j) =
      (r i : ℝ) * r j + if i = j then (r i : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j; simp; ring
    · simp [hij]
  simp_rw [hp, mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ i, ∑ j, (w i * w j) * ((r i : ℝ) * r j)) =
      (∑ i, w i * r i) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiag : (∑ i, ∑ j, (w i * w j) * (if i = j then (r i : ℝ) else 0)) =
      ∑ i, w i ^ 2 * r i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  rw [hfirst, hdiag]

theorem pi_poisson_integrable_weighted_count {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (w : ι → ℝ) :
    Integrable (fun x : ι → ℕ => ∑ i, w i * (x i : ℝ))
      (Measure.pi (fun j => poissonMeasure (r j))) := by
  exact integrable_finsetSum _ (fun i _ =>
    (pi_poisson_integrable_count r i).const_mul (w i))

theorem pi_poisson_integrable_weighted_count_sq {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (w : ι → ℝ) :
    Integrable (fun x : ι → ℕ => (∑ i, w i * (x i : ℝ)) ^ 2)
      (Measure.pi (fun j => poissonMeasure (r j))) := by
  have hex : (fun x : ι → ℕ => (∑ i, w i * (x i : ℝ)) ^ 2) =
      (fun x => ∑ i, ∑ j, (w i * w j) * ((x i : ℝ) * (x j : ℝ))) := by
    funext x
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hex]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (pi_poisson_integrable_count_product r i j).const_mul (w i * w j)))

end Rhone.Probability
