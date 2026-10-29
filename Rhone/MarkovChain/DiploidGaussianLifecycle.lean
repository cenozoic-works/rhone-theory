/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.DiploidMarginalSelection
public import Rhone.MarkovChain.DiploidGaussianApproximation
/-! # Additive multilocus diploid Gaussian viability and its integrated homolog law -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory GaussianHouseOfCards
open scoped ENNReal
noncomputable def haploidTrait (n : ℕ) (a : Fin n → ℝ) : ℝ := ∑ i, a i
noncomputable def diploidGaussianViability (n : ℕ) (S : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianFitness S (haploidTrait n p.1 + haploidTrait n p.2))
theorem haploidTrait_measurable (n : ℕ) : Measurable (haploidTrait n) :=
  Finset.measurable_sum _ (fun _ _ => measurable_pi_apply _)
theorem diploidGaussianViability_measurable (n : ℕ) (S : ℝ) :
    Measurable (diploidGaussianViability n S) := by
  unfold diploidGaussianViability gaussianFitness
  have ht := ((haploidTrait_measurable n).comp measurable_fst).add
    ((haploidTrait_measurable n).comp measurable_snd)
  exact ((ht.pow_const 2).neg.div_const (2*S)).exp.ennreal_ofReal
theorem diploidGaussianViability_marginal (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (a : Fin n → ℝ) :
    (Probability.DiploidMarginalSelection.marginalViability μ (diploidGaussianViability n S)
        a).toReal =
      marginalGaussianFitness S (μ.map (haploidTrait n)) (haploidTrait n a) := by
  have hf : Integrable (fun b => gaussianFitness S (haploidTrait n a+haploidTrait n b)) μ := by
    apply Integrable.of_bound (by
      unfold gaussianFitness
      exact ((((measurable_const.add (haploidTrait_measurable n)).pow_const 2).neg.div_const
        (2*S)).exp).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun b => by
      have hb := gaussian_fitness_bounds S hS (haploidTrait n a+haploidTrait n b)
      simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1.le] using hb.2)
  change (∫⁻ b, ENNReal.ofReal
    (gaussianFitness S (haploidTrait n a+haploidTrait n b)) ∂μ).toReal = _
  rw [← ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall (fun b =>
      (gaussian_fitness_bounds S hS (haploidTrait n a+haploidTrait n b)).1.le)),
    ENNReal.toReal_ofReal (integral_nonneg (fun b =>
      (gaussian_fitness_bounds S hS (haploidTrait n a+haploidTrait n b)).1.le))]
  rw [marginalGaussianFitness, integral_map (haploidTrait_measurable n).aemeasurable]
  unfold gaussianFitness
  fun_prop
theorem diploidGaussian_selected_probability (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure
        (Probability.DiploidMarginalSelection.selectedDiploidLaw μ
        (diploidGaussianViability n S)) := by
  have hW := diploidGaussianViability_measurable n S
  have hb (p : (Fin n → ℝ) × (Fin n → ℝ)) :
      0 < diploidGaussianViability n S p ∧ diploidGaussianViability n S p ≤ 1 := by
    have h := gaussian_fitness_bounds S hS (haploidTrait n p.1+haploidTrait n p.2)
    exact ⟨ENNReal.ofReal_pos.mpr h.1, by
      simpa only [diploidGaussianViability, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h.2⟩
  have hpos : 0 < Probability.DiploidMarginalSelection.meanViability μ
      (diploidGaussianViability n S) := by
    unfold Probability.DiploidMarginalSelection.meanViability
    rw [lintegral_pos_iff_support hW]
    have hs : Function.support (diploidGaussianViability n S) = Set.univ := by
      ext p
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (hb p).1
    rw [hs]
    simp
  have hle : Probability.DiploidMarginalSelection.meanViability μ (diploidGaussianViability n S) ≤
      1 := by
    unfold Probability.DiploidMarginalSelection.meanViability
    calc
      _ ≤ ∫⁻ _ : (Fin n → ℝ) × (Fin n → ℝ), (1 : ℝ≥0∞) ∂μ.prod μ :=
        lintegral_mono (fun p => (hb p).2)
      _ = 1 := by simp
  constructor
  rw [Probability.DiploidMarginalSelection.selectedDiploidLaw, Measure.smul_apply, withDensity_apply
      _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (ne_of_gt hpos) (ne_of_lt (hle.trans_lt (by simp)))
end Rhone.MarkovChain.DiploidMarginalSelection
