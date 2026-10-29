/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteSignedPotential
public import Rhone.Statistics.Identifiability.PositiveSurvivalTail

/-! # Proper finite-state absorption is equivalent to one finite linear system -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator ENNReal
namespace Rhone.Statistics.Identifiability.WeightedExit
variable {n : ℕ}

lemma survival_tendsto_zero_of_probability (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    [IsProbabilityMeasure (law Q α)]
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0)
    (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1) :
    Tendsto (survival Q α) atTop (𝓝 0) := by
  have hp : ∀ᵐ t ∂law Q α, 0 < t :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  apply (positive_probability_survival_tendsto_zero _ hp).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [real_Ioc Q α hQ hrow hα ht, hαsum]
  ring

lemma probability_of_survival_tendsto_zero (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0)
    (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1)
    (htail : Tendsto (survival Q α) atTop (𝓝 0)) : IsProbabilityMeasure (law Q α) := by
  have he := ac_flux_lintegral_Ioi
    (fun _ _ => (survival_contDiff Q α).contDiffOn.absolutelyContinuousOnInterval)
    (ae_of_all _ (fun t _ => survival_derivative Q α t))
    (ae_of_all _ (fun t ht => density_nonnegative Q α hQ hrow hα ht))
    (density_continuous Q α).measurable.aemeasurable.restrict htail
  constructor
  simpa [law, survival, hαsum, withDensity_apply _ MeasurableSet.univ] using he

theorem probability_iff_rowSpace (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0)
    (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1) :
    IsProbabilityMeasure (law Q α) ↔ ∃ β : Fin n → ℝ, β ᵥ* Q = α := by
  constructor
  · intro hp
    let := hp
    exact rowSpace_of_survival_tendsto_zero Q α hQ hα
      (survival_tendsto_zero_of_probability Q α hQ hrow hα hαsum)
  · intro hs
    exact probability_of_survival_tendsto_zero Q α hQ hrow hα hαsum
      (survival_tendsto_zero_of_rowSpace Q α hQ hrow hα hs)

lemma mass_one_iff_rowSpace (Q : Matrix (Fin n) (Fin n) ℝ) (α : Fin n → ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0)
    (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1) :
    law Q α univ = 1 ↔ ∃ β : Fin n → ℝ, β ᵥ* Q = α := by
  rw [← probability_iff_rowSpace Q α hQ hrow hα hαsum]
  exact ⟨fun h => ⟨h⟩, fun h => h.measure_univ⟩

end Rhone.Statistics.Identifiability.WeightedExit
