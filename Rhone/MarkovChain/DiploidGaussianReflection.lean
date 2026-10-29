/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianLifecycleBalances
/-! # Reflection preservation for the selection, Mendelian, and increment lifecycle -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

private theorem invariant_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (r : α → α) (hr : Measurable r)
    (hμ : μ.map r = μ) (W : α → ℝ≥0∞) (hW : Measurable W)
    (hw : ∀ a, W (r a) = W a) :
    (μ.withDensity W).map r = μ.withDensity W := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hr, lintegral_withDensity_eq_lintegral_mul μ hW
      (show Measurable (fun a => f (r a)) from hf.comp hr),
    lintegral_withDensity_eq_lintegral_mul μ hW hf]
  have he := lintegral_map (hW.mul hf) hr (μ := μ)
  rw [hμ] at he
  rw [he]
  apply lintegral_congr
  intro a
  simp only [Pi.mul_apply, hw]

private theorem increments_reflection (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) :
    (mutationIncrementLaw n u T).map (fun a => -a) = mutationIncrementLaw n u T := by
  have hp (i : Fin n) : IsProbabilityMeasure (locusIncrementLaw (u i) (T i)) :=
    locusIncrementLaw_probability _ _ (hu i).1 (hu i).2
  have he (i : Fin n) : (locusIncrementLaw (u i) (T i)).map (fun x => -x) =
      locusIncrementLaw (u i) (T i) := by
    rw [locusIncrementLaw, Measure.map_add _ _ measurable_neg,
      Measure.map_smul _ measurable_neg.aemeasurable,
      Measure.map_smul _ measurable_neg.aemeasurable,
      Measure.map_dirac' measurable_neg, gaussianReal_map_neg]
    simp
  change (Measure.pi _).map (fun a i => -(a i)) = _
  rw [Measure.pi_map_pi (fun i => measurable_neg.aemeasurable)]
  simp_rw [he]
  rfl

private theorem selected_reflection (n : ℕ) (S : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun a => -a) = μ) :
    (Probability.DiploidMarginalSelection.selectedDiploidLaw μ (diploidGaussianViability n S)).map
      (Prod.map (fun a => -a) (fun a => -a)) =
      Probability.DiploidMarginalSelection.selectedDiploidLaw μ (diploidGaussianViability n S) := by
  have hr : Measurable (fun a : Fin n → ℝ => -a) := by fun_prop
  have hp : (μ.prod μ).map (Prod.map (fun a => -a) (fun a => -a)) = μ.prod μ := by
    rw [← Measure.map_prod_map μ μ hr hr, hsym]
  have hw (p : (Fin n → ℝ) × (Fin n → ℝ)) :
      diploidGaussianViability n S (Prod.map (fun a => -a) (fun a => -a) p) =
      diploidGaussianViability n S p := by
    have ht (a : Fin n → ℝ) : haploidTrait n (-a) = -haploidTrait n a := by
      simp [haploidTrait]
    simp only [Prod.map, diploidGaussianViability, ht,
      GaussianHouseOfCards.gaussianFitness]
    rw [← neg_add, neg_sq]
  rw [Probability.DiploidMarginalSelection.selectedDiploidLaw, Measure.map_smul _
      (hr.prodMap hr).aemeasurable,
    invariant_density _ _ (hr.prodMap hr) hp _ (diploidGaussianViability_measurable n S) hw]

private theorem gamete_reflection (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun a => -a) = μ) :
    (Probability.DiploidMarginalSelection.mendelianGameteLaw n μ (diploidGaussianViability n S)).map
        (fun a => -a) =
      Probability.DiploidMarginalSelection.mendelianGameteLaw n μ (diploidGaussianViability n S) :=
          by
  have := diploidGaussian_selected_probability n S hS μ
  let c := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → Fin 2) =>
    fun j => if p.2 j = 0 then p.1.1 j else p.1.2 j
  let r := Prod.map (Prod.map (fun a : Fin n → ℝ => -a) (fun a : Fin n → ℝ => -a))
    (id : (Fin n → Fin 2) → (Fin n → Fin 2))
  have hc : Measurable c := by
    apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_pi_apply j).comp measurable_fst.fst).ite
      (measurableSet_eq.preimage ((measurable_pi_apply j).comp measurable_snd))
      ((measurable_pi_apply j).comp measurable_fst.snd)
  have hr : Measurable r := by fun_prop
  have hp : ((Probability.DiploidMarginalSelection.selectedDiploidLaw μ
      (diploidGaussianViability n S)).prod
      (Probability.DiploidMarginalSelection.meiosisMaskLaw n)).map r =
      (Probability.DiploidMarginalSelection.selectedDiploidLaw μ
          (diploidGaussianViability n S)).prod
          (Probability.DiploidMarginalSelection.meiosisMaskLaw n) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
      selected_reflection n S μ hsym, Measure.map_id]
  change (Measure.map c _).map (fun a => -a) = Measure.map c _
  rw [Measure.map_map (by fun_prop) hc]
  have he : (fun a : Fin n → ℝ => -a) ∘ c = c ∘ r := by
    funext p j
    by_cases hj : p.2 j = 0 <;> simp [c, r, hj]
  rw [he, ← Measure.map_map hc hr, hp]

private theorem mutation_reflection (n : ℕ) (u : Fin n → ℝ)
    (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun a => -a) = μ) :
    (gaussianIncrementMutation n u T μ).map (fun a => -a) =
      gaussianIncrementMutation n u T μ := by
  have := mutationIncrementLaw_probability n u T hu
  have hr : Measurable (fun a : Fin n → ℝ => -a) := by fun_prop
  have hp : (μ.prod (mutationIncrementLaw n u T)).map
      (Prod.map (fun a => -a) (fun a => -a)) = μ.prod (mutationIncrementLaw n u T) := by
    rw [← Measure.map_prod_map _ _ hr hr, hsym, increments_reflection n u T hu]
  rw [gaussianIncrementMutation, Measure.map_map hr (haplotypeAddition_measurable n)]
  have he : (fun a : Fin n → ℝ => -a) ∘
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i+p.2 i) =
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => p.1 i+p.2 i) ∘
        Prod.map (fun a => -a) (fun a => -a) := by
    funext p i
    simp [add_comm]
  rw [he, ← Measure.map_map (haplotypeAddition_measurable n) (hr.prodMap hr), hp]

theorem diploidGaussianLifecycleUpdate_reflection (n : ℕ) (S : ℝ) (hS : 0 < S)
    (u : Fin n → ℝ) (T : Fin n → ℝ≥0) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun a => -a) = μ) :
    (diploidGaussianLifecycleUpdate n S u T μ).map (fun a => -a) =
      diploidGaussianLifecycleUpdate n S u T μ := by
  have := diploidGaussian_gamete_probability n S hS μ
  exact mutation_reflection n u T hu _ (gamete_reflection n S hS μ hsym)

theorem reflection_coordinate_integral_zero (n : ℕ)
    (μ : Measure (Fin n → ℝ))
    (hsym : μ.map (fun a => -a) = μ)
    (i : Fin n) (hi : Integrable (fun a => a i) μ) :
    (∫ a, a i ∂μ) = 0 := by
  have he := integral_map (μ := μ) (φ := fun a : Fin n → ℝ => -a)
    (by fun_prop) (by rw [hsym]; exact hi.aestronglyMeasurable)
  rw [hsym] at he
  change (∫ a, a i ∂μ) = ∫ a, -(a i) ∂μ at he
  rw [integral_neg] at he
  linarith
end Rhone.MarkovChain.DiploidMarginalSelection
