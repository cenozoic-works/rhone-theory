/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.FinitePoissonCounts
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Generating function of a Poisson count and the law of a sum of independent counts

Source: watterson1975, p. 264, eq. (2.2). -/

@[expose] public section
namespace Rhone.Probability
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

theorem poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro k
  rw [poissonMeasure_singleton, Measure.dirac_apply' _ (measurableSet_singleton k)]
  rcases k with _ | k
  · simp
  · have hk : (0 : ℕ) ∉ ({k + 1} : Set ℕ) := by simp
    rw [Set.indicator_of_notMem hk]
    simp

/-- Source: watterson1975, p. 264, eq. (2.2). -/
theorem pi_poisson_hasLaw_finsetSum {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) (s : Finset ι) :
    HasLaw (fun x : ι → ℕ => ∑ i ∈ s, x i) (poissonMeasure (∑ i ∈ s, r i))
      (Measure.pi (fun j => poissonMeasure (r j))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by fun_prop, ?_⟩
    simp only [sum_empty]
    rw [Measure.map_const, measure_univ, one_smul, poissonMeasure_zero_eq_dirac]
  | insert a s ha ih =>
    have hind : iIndepFun (fun i (x : ι → ℕ) => x i)
        (Measure.pi (fun j => poissonMeasure (r j))) :=
      iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    have hsa := hind.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i) ha
    have hla : HasLaw (fun x : ι → ℕ => x a) (poissonMeasure (r a))
        (Measure.pi (fun j => poissonMeasure (r j))) :=
      ⟨(measurable_pi_apply a).aemeasurable,
        (measurePreserving_eval (fun j => poissonMeasure (r j)) a).map_eq⟩
    have hsum : (∑ j ∈ s, fun x : ι → ℕ => x j) = fun x : ι → ℕ => ∑ i ∈ s, x i := by
      funext x
      simp only [Finset.sum_apply]
    rw [hsum] at hsa
    have h := hsa.hasLaw_add_poissonMeasure ih hla
    have hfun : (fun x : ι → ℕ => ∑ i ∈ insert a s, x i) =
        (fun x : ι → ℕ => ∑ i ∈ s, x i) + fun x : ι → ℕ => x a := by
      funext x
      simp only [sum_insert ha, Pi.add_apply]
      exact add_comm _ _
    rw [hfun, sum_insert ha, add_comm (r a)]
    exact h

/-- Source: watterson1975, p. 264, eq. (2.2). -/
theorem pi_poisson_map_sum {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) :
    (Measure.pi (fun j => poissonMeasure (r j))).map (fun x : ι → ℕ => ∑ i, x i) =
      poissonMeasure (∑ i, r i) :=
  (pi_poisson_hasLaw_finsetSum r univ).map_eq

/-- Source: watterson1975, p. 264. -/
theorem poisson_integral_pow (r : ℝ≥0) (z : ℝ) :
    ∫ k : ℕ, z ^ k ∂poissonMeasure r = Real.exp (-((r : ℝ) * (1 - z))) := by
  have hint : Integrable (fun k : ℕ => z ^ k) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    have hs := (Real.summable_pow_div_factorial ((r : ℝ) * |z|)).mul_left (Real.exp (-(r : ℝ)))
    refine hs.congr fun k => ?_
    rw [norm_pow, Real.norm_eq_abs, mul_pow]
    ring
  have h1 := hasSum_integral_poissonMeasure hint
  have h2 := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * z)).mul_left
    (Real.exp (-(r : ℝ)))
  have he : (fun k : ℕ => (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ)) • z ^ k) =
      fun k : ℕ => Real.exp (-(r : ℝ)) * (((r : ℝ) * z) ^ k / (k.factorial : ℝ)) := by
    funext k
    rw [smul_eq_mul, mul_pow]
    ring
  rw [he] at h1
  rw [h1.unique h2, ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  congr 1
  ring

/-- Source: watterson1975, p. 264, eq. (2.2). -/
theorem pi_poisson_integral_pow_sum {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) (z : ℝ) :
    ∫ x : ι → ℕ, z ^ (∑ i, x i) ∂Measure.pi (fun j => poissonMeasure (r j)) =
      Real.exp (-((∑ i, (r i : ℝ)) * (1 - z))) := by
  have hm := integral_map (μ := Measure.pi (fun j => poissonMeasure (r j)))
    (φ := fun x : ι → ℕ => ∑ i, x i) (f := fun k : ℕ => z ^ k)
    (Measurable.of_discrete).aemeasurable Measurable.of_discrete.aestronglyMeasurable
  rw [pi_poisson_map_sum] at hm
  rw [← hm, poisson_integral_pow, NNReal.coe_sum]

/-- Source: watterson1975, p. 264, eq. (2.2). -/
theorem pi_poisson_real_sum_eq {ι : Type*} [Fintype ι] (r : ι → ℝ≥0) (k : ℕ) :
    (Measure.pi (fun j => poissonMeasure (r j))).real {x : ι → ℕ | ∑ i, x i = k} =
      Real.exp (-(∑ i, (r i : ℝ))) * (∑ i, (r i : ℝ)) ^ k / (k.factorial : ℝ) := by
  have hm : (Measure.pi (fun j => poissonMeasure (r j))).real {x : ι → ℕ | ∑ i, x i = k} =
      ((Measure.pi (fun j => poissonMeasure (r j))).map (fun x : ι → ℕ => ∑ i, x i)).real
        {k} := by
    rw [map_measureReal_apply Measurable.of_discrete (measurableSet_singleton k)]
    rfl
  rw [hm, pi_poisson_map_sum, poissonMeasure_real_singleton, NNReal.coe_sum]

end Rhone.Probability
