/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianLifecycle
public import Mathlib.Probability.Kernel.CondDistrib
/-! # The selected locus marginal density conditioned on its focal coordinate -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem selectedGaussian_locus_conditional_density_candidate
    (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (i : Fin n) :
    (Probability.DiploidMarginalSelection.selectedDiploidLaw μ (diploidGaussianViability n S)).map
        (fun p => p.1 i) =
      (Probability.DiploidMarginalSelection.meanViability μ (diploidGaussianViability n S))⁻¹ •
        (μ.map (fun a => a i)).withDensity (fun x =>
          ∫⁻ a, Probability.DiploidMarginalSelection.marginalViability μ
              (diploidGaussianViability n S) a
            ∂ProbabilityTheory.condDistrib
              (id : (Fin n → ℝ) → (Fin n → ℝ)) (fun a => a i) μ x)
 := by
  have := diploidGaussian_selected_probability n S hS μ
  have hW := diploidGaussianViability_measurable n S
  have hm : Measurable
      (Probability.DiploidMarginalSelection.marginalViability μ (diploidGaussianViability n S)) :=
    hW.lintegral_prod_right'
  let κ := condDistrib (id : (Fin n → ℝ) → (Fin n → ℝ)) (fun a => a i) μ
  have hd : Measurable (fun x => ∫⁻ a,
      Probability.DiploidMarginalSelection.marginalViability μ (diploidGaussianViability n S) a ∂κ
          x) := by
    exact hm.lintegral_kernel
  have he : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 i) =
      (fun a => a i) ∘ Prod.fst := rfl
  rw [he, ← Measure.map_map (measurable_pi_apply i) measurable_fst,
    Probability.DiploidMarginalSelection.selectedDiploidLaw_fst μ _ hW, Measure.map_smul _
        (measurable_pi_apply i).aemeasurable]
  congr 1
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_pi_apply i),
    lintegral_withDensity_eq_lintegral_mul μ hm
      (show Measurable (fun a => f (a i)) from hf.comp (measurable_pi_apply i)),
    lintegral_withDensity_eq_lintegral_mul _ hd hf]
  have hg : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      Probability.DiploidMarginalSelection.marginalViability μ (diploidGaussianViability n S) p.2*f
          p.1) :=
    (hm.comp measurable_snd).mul (hf.comp measurable_fst)
  have hc := compProd_map_condDistrib (μ := μ)
    (measurable_pi_apply i).aemeasurable measurable_id.aemeasurable
  have hi := Measure.lintegral_compProd (μ := μ.map (fun a => a i)) (κ := κ) hg
  rw [hc, lintegral_map hg (by fun_prop)] at hi
  simp only [id_eq, Pi.mul_apply] at hi ⊢
  rw [hi]
  apply lintegral_congr
  intro x
  exact lintegral_mul_const (f x) hm
end Rhone.MarkovChain.DiploidMarginalSelection
