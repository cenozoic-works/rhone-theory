/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Prod
/-! # Marginal law of a selected diploid pair and the Mendelian homolog law -/

@[expose] public section
namespace Rhone.Probability.DiploidMarginalSelection
open MeasureTheory
open scoped ENNReal
noncomputable def meanViability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (W : α × α → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ p, W p ∂μ.prod μ
noncomputable def selectedDiploidLaw {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (W : α × α → ℝ≥0∞) : Measure (α × α) :=
  (meanViability μ W)⁻¹ • (μ.prod μ).withDensity W
noncomputable def marginalViability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (W : α × α → ℝ≥0∞) (a : α) : ℝ≥0∞ :=
  ∫⁻ b, W (a, b) ∂μ
noncomputable def mendelianHomologLaw {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (W : α × α → ℝ≥0∞) : Measure α :=
  (2 : ℝ≥0∞)⁻¹ • (selectedDiploidLaw μ W).map Prod.fst +
  (2 : ℝ≥0∞)⁻¹ • (selectedDiploidLaw μ W).map Prod.snd
theorem selectedDiploidLaw_fst {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (W : α × α → ℝ≥0∞)
    (hW : Measurable W) :
    (selectedDiploidLaw μ W).map Prod.fst =
      (meanViability μ W)⁻¹ • μ.withDensity (marginalViability μ W) := by
  rw [selectedDiploidLaw, Measure.map_smul _ measurable_fst.aemeasurable]
  congr 1
  ext A hA
  rw [Measure.map_apply measurable_fst hA, withDensity_apply _ (measurable_fst hA),
    withDensity_apply _ hA]
  rw [← lintegral_indicator (measurable_fst hA), ← lintegral_indicator hA]
  rw [lintegral_prod _]
  · apply lintegral_congr
    intro a
    by_cases ha : a ∈ A
    · simp [Set.indicator, ha, marginalViability]
    · simp [Set.indicator, ha]
  · exact (hW.indicator (measurable_fst hA)).aemeasurable
theorem mendelianHomologLaw_eq_marginal {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (W : α × α → ℝ≥0∞)
    (hW : Measurable W) (hsym : ∀ a b, W (a, b) = W (b, a)) :
    mendelianHomologLaw μ W =
      (meanViability μ W)⁻¹ • μ.withDensity (marginalViability μ W) := by
  have hsnd : (selectedDiploidLaw μ W).map Prod.snd =
      (meanViability μ W)⁻¹ • μ.withDensity (marginalViability μ W) := by
    rw [selectedDiploidLaw, Measure.map_smul _ measurable_snd.aemeasurable]
    congr 1
    ext A hA
    rw [Measure.map_apply measurable_snd hA, withDensity_apply _ (measurable_snd hA),
      withDensity_apply _ hA]
    rw [← lintegral_indicator (measurable_snd hA), ← lintegral_indicator hA,
      lintegral_prod_symm' _ (hW.indicator (measurable_snd hA))]
    apply lintegral_congr
    intro a
    by_cases ha : a ∈ A
    · simp only [Set.indicator, Set.mem_preimage, ha, ite_eq_left, marginalViability]
      apply lintegral_congr
      intro b
      exact hsym b a
    · simp [Set.indicator, ha]
  rw [mendelianHomologLaw, selectedDiploidLaw_fst μ W hW, hsnd, ← add_smul]
  have hh : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [hh, one_smul]
end Rhone.Probability.DiploidMarginalSelection
