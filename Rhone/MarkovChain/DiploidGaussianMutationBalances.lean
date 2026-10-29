/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianIncrementMoments
/-! # Exact increment mutation balances on the full haplotype law -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem haplotypeAddition_measurable (n : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i+p.2 i) := by
  fun_prop

theorem gaussianIncrementMutation_integrable_sq (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (i : Fin n) :
    Integrable (fun a => (a i) ^ 2) (gaussianIncrementMutation n u T μ) := by
  have := mutationIncrementLaw_probability n u T hu
  have hm : MemLp (fun a => a i) 2 μ :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable).mpr (h2 i)
  have he : MemLp (fun e => e i) 2 (mutationIncrementLaw n u T) :=
    (memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable).mpr
      (mutationIncrementLaw_integrable_sq n u T hu i)
  unfold gaussianIncrementMutation
  have hs : Measurable (fun a : Fin n → ℝ => (a i) ^ 2) := by fun_prop
  apply (integrable_map_measure hs.aestronglyMeasurable
      (haplotypeAddition_measurable n).aemeasurable).mpr
  exact ((hm.comp_fst _).add (he.comp_snd _)).integrable_sq

theorem gaussianIncrementMutation_mean (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (i : Fin n) :
    (∫ a, a i ∂gaussianIncrementMutation n u T μ) = ∫ a, a i ∂μ := by
  have := mutationIncrementLaw_probability n u T hu
  have hm := firstMoment_of_secondMoment μ (fun a => a i) (measurable_pi_apply i) (h2 i)
  have he := firstMoment_of_secondMoment (mutationIncrementLaw n u T)
    (fun e => e i) (measurable_pi_apply i) (mutationIncrementLaw_integrable_sq n u T hu i)
  rw [gaussianIncrementMutation, integral_map (haplotypeAddition_measurable n).aemeasurable
    (measurable_pi_apply i).aestronglyMeasurable]
  change (∫ p, p.1 i+p.2 i ∂μ.prod (mutationIncrementLaw n u T)) = _
  rw [integral_add (hm.comp_fst _) (he.comp_snd _), integral_fun_fst (fun a : Fin n → ℝ => a i),
    integral_fun_snd (fun e : Fin n → ℝ => e i), mutationIncrementLaw_mean n u T hu i]
  simp

theorem gaussianIncrementMutation_second (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (i : Fin n) :
    (∫ a, (a i) ^ 2 ∂gaussianIncrementMutation n u T μ) =
      (∫ a, (a i) ^ 2 ∂μ)+u i*(T i : ℝ) := by
  have := mutationIncrementLaw_probability n u T hu
  have hm := firstMoment_of_secondMoment μ (fun a => a i) (measurable_pi_apply i) (h2 i)
  have he2 := mutationIncrementLaw_integrable_sq n u T hu i
  have he := firstMoment_of_secondMoment (mutationIncrementLaw n u T)
    (fun e => e i) (measurable_pi_apply i) he2
  have hc := hm.mul_prod he
  rw [gaussianIncrementMutation, integral_map (haplotypeAddition_measurable n).aemeasurable
    ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable]
  change (∫ p, (p.1 i+p.2 i) ^ 2 ∂μ.prod (mutationIncrementLaw n u T)) = _
  have hexp : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 i+p.2 i) ^ 2) =
      (fun p => (p.1 i) ^ 2+2*(p.1 i*p.2 i)+(p.2 i) ^ 2) := by funext p; ring
  have hsum : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (p.1 i) ^ 2+2*(p.1 i*p.2 i)) (μ.prod (mutationIncrementLaw n u T)) := by
    exact ((h2 i).comp_fst _).add (hc.const_mul 2)
  rw [hexp, integral_add hsum (he2.comp_snd _),
    integral_add ((h2 i).comp_fst _) (hc.const_mul 2), integral_const_mul,
    integral_fun_fst (fun a : Fin n → ℝ => (a i) ^ 2),
    integral_fun_snd (fun e : Fin n → ℝ => (e i) ^ 2),
    integral_prod_mul (fun a : Fin n → ℝ => a i) (fun e : Fin n → ℝ => e i),
    mutationIncrementLaw_mean n u T hu i, mutationIncrementLaw_second n u T hu i]
  simp

theorem gaussianIncrementMutation_cross (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ a, a i*a j ∂gaussianIncrementMutation n u T μ) = ∫ a, a i*a j ∂μ := by
  have := mutationIncrementLaw_probability n u T hu
  have hm (k : Fin n) := firstMoment_of_secondMoment μ
    (fun a => a k) (measurable_pi_apply k) (h2 k)
  have he2 := mutationIncrementLaw_integrable_sq n u T hu
  have he (k : Fin n) := firstMoment_of_secondMoment (mutationIncrementLaw n u T)
    (fun e => e k) (measurable_pi_apply k) (he2 k)
  have hmc := crossMoment_of_secondMoments μ (fun a => a i) (fun a => a j)
    (measurable_pi_apply i) (measurable_pi_apply j) (h2 i) (h2 j)
  have hec := crossMoment_of_secondMoments (mutationIncrementLaw n u T)
    (fun e => e i) (fun e => e j) (measurable_pi_apply i) (measurable_pi_apply j) (he2 i) (he2 j)
  have hmi := (hm i).mul_prod (he j)
  have hmj := (hm j).mul_prod (he i)
  have hobs : Measurable (fun a : Fin n → ℝ => a i*a j) := by fun_prop
  rw [gaussianIncrementMutation, integral_map (haplotypeAddition_measurable n).aemeasurable
    hobs.aestronglyMeasurable]
  change (∫ p, (p.1 i+p.2 i)*(p.1 j+p.2 j) ∂μ.prod (mutationIncrementLaw n u T)) = _
  have hexp : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 i+p.2 i)*(p.1 j+p.2 j)) =
      (fun p => p.1 i*p.1 j+p.1 i*p.2 j+p.1 j*p.2 i+p.2 i*p.2 j) := by funext p; ring
  have hsum : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      p.1 i*p.1 j+p.1 i*p.2 j) (μ.prod (mutationIncrementLaw n u T)) := by
    exact (hmc.comp_fst _).add hmi
  have hsum2 : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      p.1 i*p.1 j+p.1 i*p.2 j+p.1 j*p.2 i) (μ.prod (mutationIncrementLaw n u T)) := by
    exact hsum.add hmj
  rw [hexp, integral_add hsum2 (hec.comp_snd _), integral_add hsum hmj,
    integral_add (hmc.comp_fst _) hmi,
    integral_fun_fst (fun a : Fin n → ℝ => a i*a j),
    integral_fun_snd (fun e : Fin n → ℝ => e i*e j),
    integral_prod_mul (fun a : Fin n → ℝ => a i) (fun e : Fin n → ℝ => e j),
    integral_prod_mul (fun a : Fin n → ℝ => a j) (fun e : Fin n → ℝ => e i),
    mutationIncrementLaw_mean n u T hu i, mutationIncrementLaw_mean n u T hu j,
    mutationIncrementLaw_cross n u T hu i j hij]
  simp

end Rhone.MarkovChain.DiploidMarginalSelection
