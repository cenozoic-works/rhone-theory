/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianMutationBalances
/-! # Finite moments of the selected-parent and freely assorting gamete laws -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory GaussianHouseOfCards
open scoped ENNReal NNReal

theorem diploidGaussianViability_le_one (n : ℕ) (S : ℝ) (hS : 0 < S)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : diploidGaussianViability n S p ≤ 1 := by
  have hb := (gaussian_fitness_bounds S hS (haploidTrait n p.1+haploidTrait n p.2)).2
  simpa only [diploidGaussianViability, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hb

theorem diploidGaussianMean_ne_zero (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    Probability.DiploidMarginalSelection.meanViability μ (diploidGaussianViability n S) ≠ 0 := by
  have hW := diploidGaussianViability_measurable n S
  have hp (p : (Fin n → ℝ) × (Fin n → ℝ)) : 0 < diploidGaussianViability n S p :=
    ENNReal.ofReal_pos.mpr
      (gaussian_fitness_bounds S hS (haploidTrait n p.1+haploidTrait n p.2)).1
  have hs : Function.support (diploidGaussianViability n S) = Set.univ := by
    ext p
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hp p)
  apply ne_of_gt
  unfold Probability.DiploidMarginalSelection.meanViability
  rw [lintegral_pos_iff_support hW, hs]
  simp

theorem diploidGaussianSelected_integrable (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (hf : Integrable f (μ.prod μ)) :
    Integrable f (Probability.DiploidMarginalSelection.selectedDiploidLaw μ
        (diploidGaussianViability n S)) := by
  have hd : (μ.prod μ).withDensity (diploidGaussianViability n S) ≤ μ.prod μ := by
    calc
      _ ≤ (μ.prod μ).withDensity 1 := withDensity_mono
        (Filter.Eventually.of_forall (diploidGaussianViability_le_one n S hS))
      _ = _ := withDensity_one
  exact (hf.mono_measure hd).smul_measure
    (ENNReal.inv_ne_top.mpr (diploidGaussianMean_ne_zero n S hS μ))

theorem diploidGaussianSelected_integrable_sq (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (i : Fin n) :
    Integrable (fun p => (p.1 i) ^ 2)
        (Probability.DiploidMarginalSelection.selectedDiploidLaw μ (diploidGaussianViability n S)) ∧
    Integrable (fun p => (p.2 i) ^ 2)
        (Probability.DiploidMarginalSelection.selectedDiploidLaw μ
        (diploidGaussianViability n S)) :=
  ⟨diploidGaussianSelected_integrable n S hS μ _ ((h2 i).comp_fst μ),
    diploidGaussianSelected_integrable n S hS μ _ ((h2 i).comp_snd μ)⟩

theorem diploidGaussianGamete_integrable_sq (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h2 : ∀ i, Integrable (fun a => (a i) ^ 2) μ) (i : Fin n) :
    Integrable (fun a => (a i) ^ 2)
      (Probability.DiploidMarginalSelection.mendelianGameteLaw n μ
          (diploidGaussianViability n S)) := by
  have hs := diploidGaussianSelected_integrable_sq n S hS μ h2 i
  have := diploidGaussian_selected_probability n S hS μ
  have hchoose : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → Fin 2) =>
      fun j => if p.2 j = 0 then p.1.1 j else p.1.2 j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_pi_apply j).comp measurable_fst.fst).ite
      (measurableSet_eq.preimage ((measurable_pi_apply j).comp measurable_snd))
      ((measurable_pi_apply j).comp measurable_fst.snd)
  have hi : Integrable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → Fin 2) =>
      (if p.2 i = 0 then p.1.1 i else p.1.2 i) ^ 2)
      ((Probability.DiploidMarginalSelection.selectedDiploidLaw μ
          (diploidGaussianViability n S)).prod
          (Probability.DiploidMarginalSelection.meiosisMaskLaw n)) := by
    apply ((hs.1.comp_fst (Probability.DiploidMarginalSelection.meiosisMaskLaw n)).add
        (hs.2.comp_fst (Probability.DiploidMarginalSelection.meiosisMaskLaw n))).mono'
      (by
        have hm : Measurable (fun a : Fin n → ℝ => (a i) ^ 2) := by fun_prop
        exact (hm.comp hchoose).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun p => by
      change ‖(if p.2 i = 0 then p.1.1 i else p.1.2 i) ^ 2‖ ≤
        (p.1.1 i) ^ 2+(p.1.2 i) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      split_ifs <;> nlinarith [sq_nonneg (p.1.1 i), sq_nonneg (p.1.2 i)])
  unfold Probability.DiploidMarginalSelection.mendelianGameteLaw
  have hm : Measurable (fun a : Fin n → ℝ => (a i) ^ 2) := by fun_prop
  exact (integrable_map_measure hm.aestronglyMeasurable hchoose.aemeasurable).mpr hi

end Rhone.MarkovChain.DiploidMarginalSelection
