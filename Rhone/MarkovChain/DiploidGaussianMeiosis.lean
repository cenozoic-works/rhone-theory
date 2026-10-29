/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianLifecycle
public import Rhone.Probability.DiploidMendelianMarginal
/-! # Multilocus Gaussian Mendelian laws and marginal viability bounds -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory
theorem diploidGaussianViability_symm (n : ℕ) (S : ℝ) (a b : Fin n → ℝ) :
    diploidGaussianViability n S (a, b) = diploidGaussianViability n S (b, a) := by
  unfold diploidGaussianViability
  rw [add_comm]
theorem diploidGaussian_gamete_probability (n : ℕ) (S : ℝ) (hS : 0 < S)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure
        (Probability.DiploidMarginalSelection.mendelianGameteLaw n μ
        (diploidGaussianViability n S)) := by
  have := diploidGaussian_selected_probability n S hS μ
  have hchoose : Measurable (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → Fin 2) =>
      fun j => if p.2 j = 0 then p.1.1 j else p.1.2 j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_pi_apply j).comp measurable_fst.fst).ite
      (measurableSet_eq.preimage ((measurable_pi_apply j).comp measurable_snd))
      ((measurable_pi_apply j).comp measurable_fst.snd)
  exact (Measure.isProbabilityMeasure_map_iff hchoose.aemeasurable).mpr inferInstance
end Rhone.MarkovChain.DiploidMarginalSelection
