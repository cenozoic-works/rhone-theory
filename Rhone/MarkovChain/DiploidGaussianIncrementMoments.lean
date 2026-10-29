/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianIncrementLaw
/-! # Gaussian increment moments and finite haplotype coordinate moments -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem firstMoment_of_secondMoment {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (h2 : Integrable (fun a => (f a) ^ 2) μ) : Integrable f μ := by
  exact ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr h2).integrable (by norm_num)

theorem crossMoment_of_secondMoments {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun a => (f a) ^ 2) μ)
    (hg2 : Integrable (fun a => (g a) ^ 2) μ) : Integrable (fun a => f a*g a) μ := by
  apply (hf2.add hg2).mono' (hf.mul hg).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a => by
    change ‖f a*g a‖ ≤ (f a) ^ 2+(g a) ^ 2
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|f a|-|g a|), sq_abs (f a), sq_abs (g a)])

theorem locusIncrementLaw_integrable_sq (u : ℝ) (T : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (locusIncrementLaw u T) := by
  rw [locusIncrementLaw, integrable_add_measure]
  exact ⟨(integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top,
    (memLp_id_gaussianReal (μ := 0) (v := T) 2).integrable_sq.smul_measure
      ENNReal.ofReal_ne_top⟩

theorem locusIncrementLaw_mean (u : ℝ) (T : ℝ≥0) :
    (∫ x, x ∂locusIncrementLaw u T) = 0 := by
  have hd : Integrable (fun x : ℝ => x) (Measure.dirac (0 : ℝ)) :=
    integrable_dirac (by simp)
  have hg : Integrable (fun x : ℝ => x) (gaussianReal 0 T) :=
    (memLp_id_gaussianReal (μ := 0) (v := T) 1).integrable (by norm_num)
  rw [locusIncrementLaw, integral_add_measure
    (hd.smul_measure ENNReal.ofReal_ne_top) (hg.smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure]

theorem locusIncrementLaw_second (u : ℝ) (T : ℝ≥0) (hu : 0 ≤ u) :
    (∫ x, x ^ 2 ∂locusIncrementLaw u T) = u*(T : ℝ) := by
  have hd : Integrable (fun x : ℝ => x ^ 2) (Measure.dirac (0 : ℝ)) :=
    integrable_dirac (by simp)
  have hg := (memLp_id_gaussianReal (μ := 0) (v := T) 2).integrable_sq
  have he : (∫ x, x ^ 2 ∂gaussianReal 0 T) = (T : ℝ) := by
    have hv := variance_fun_id_gaussianReal (μ := 0) (v := T)
    change Var[id; gaussianReal 0 T] = (T : ℝ) at hv
    rw [variance_eq_integral measurable_id.aemeasurable] at hv
    simpa only [integral_id_gaussianReal, id_eq, sub_zero] using hv
  rw [locusIncrementLaw, integral_add_measure
    (hd.smul_measure ENNReal.ofReal_ne_top) (hg.smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure, he, ENNReal.toReal_ofReal hu]

theorem mutationIncrementLaw_eval (n : ℕ) (u : Fin n → ℝ) (T : Fin n → ℝ≥0)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (i : Fin n) :
    (mutationIncrementLaw n u T).map (fun e => e i) = locusIncrementLaw (u i) (T i) := by
  have (j : Fin n) : IsProbabilityMeasure (locusIncrementLaw (u j) (T j)) :=
    locusIncrementLaw_probability _ _ (hu j).1 (hu j).2
  exact (measurePreserving_eval (fun j => locusIncrementLaw (u j) (T j)) i).map_eq

theorem mutationIncrementLaw_integrable_sq (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (i : Fin n) :
    Integrable (fun e => (e i) ^ 2) (mutationIncrementLaw n u T) := by
  have hi := locusIncrementLaw_integrable_sq (u i) (T i)
  rw [← mutationIncrementLaw_eval n u T hu i] at hi
  have hs : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  exact (integrable_map_measure hs.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).mp hi

theorem mutationIncrementLaw_mean (n : ℕ) (u : Fin n → ℝ) (T : Fin n → ℝ≥0)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (i : Fin n) :
    (∫ e, e i ∂mutationIncrementLaw n u T) = 0 := by
  rw [← locusIncrementLaw_mean (u i) (T i), ← mutationIncrementLaw_eval n u T hu i,
    integral_map (measurable_pi_apply i).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x) _)]

theorem mutationIncrementLaw_second (n : ℕ) (u : Fin n → ℝ) (T : Fin n → ℝ≥0)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (i : Fin n) :
    (∫ e, (e i) ^ 2 ∂mutationIncrementLaw n u T) = u i*(T i : ℝ) := by
  rw [← locusIncrementLaw_second (u i) (T i) (hu i).1,
    ← mutationIncrementLaw_eval n u T hu i, integral_map (measurable_pi_apply i).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) _)]

theorem mutationIncrementLaw_independent (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (i j : Fin n) (hij : i ≠ j) :
    IndepFun (fun e => e i) (fun e => e j) (mutationIncrementLaw n u T) := by
  have (k : Fin n) : IsProbabilityMeasure (locusIncrementLaw (u k) (T k)) :=
    locusIncrementLaw_probability _ _ (hu k).1 (hu k).2
  exact (iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).indepFun hij

theorem mutationIncrementLaw_cross (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ e, e i*e j ∂mutationIncrementLaw n u T) = 0 := by
  rw [(mutationIncrementLaw_independent n u T hu i j hij).integral_fun_mul_eq_mul_integral
    (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable,
    mutationIncrementLaw_mean n u T hu i]
  simp

end Rhone.MarkovChain.DiploidMarginalSelection
