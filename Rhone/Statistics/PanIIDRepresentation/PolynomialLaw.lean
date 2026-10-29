/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PanIIDRepresentation.SelectedLaw
public import Rhone.Statistics.AtomicSmoothing.ClippedClock

/-! # Polynomial moment equality for the pan three-sample genealogy -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.PanIIDRepresentation
open AtomicRank AtomicSmoothing Algebra.Identifiability MarkovChain.Identifiability Identifiability

def clockFeature (f : Coefficients) (p : ℝ × ℝ) : ℝ :=
  value f (unitClock p.1) (unitClock p.2)

lemma clockFeature_continuous (f : Coefficients) : Continuous (clockFeature f) := by
  have h : Continuous (fun p : ℝ × ℝ => (unitClock p.1, unitClock p.2)) :=
    (unitClock_lipschitz.continuous.comp continuous_fst).prodMk
      (unitClock_lipschitz.continuous.comp continuous_snd)
  exact (value_continuous f).comp h

lemma clockFeature_bound (f : Coefficients) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p, ‖clockFeature f p‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (K := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (value_continuous f).norm.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun p => ?_⟩
  apply le_trans _ (le_max_left M 0)
  apply hM
  exact ⟨(unitClock p.1, unitClock p.2),
    ⟨⟨(unitClock_positive p.1).le, unitClock_le_one p.1⟩,
      ⟨(unitClock_positive p.2).le, unitClock_le_one p.2⟩⟩, rfl⟩

lemma selected_clock_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (f : Coefficients) :
    Integrable (fun p : LeftCube =>
      selectedKernel (fun x y => clockFeature f (x, y)) p.1.1 p.1.2 p.2)
      ((μ.prod μ).prod μ) := by
  obtain ⟨M, hM, hb⟩ := clockFeature_bound f
  have hm : Measurable (fun p : LeftCube =>
      selectedKernel (fun x y => clockFeature f (x, y)) p.1.1 p.1.2 p.2) := by
    unfold selectedKernel
    exact ((clockFeature_continuous f).measurable.comp (by fun_prop)).ite
      (by measurability) measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable M
  apply Filter.Eventually.of_forall
  intro p
  unfold selectedKernel
  split_ifs
  · exact hb _
  · simpa only [norm_zero] using hM

theorem pan_polynomial_iid (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    (f : Coefficients) :
    (∫ p, clockFeature f p ∂PanThreeSample.law r) =
      ∫ p : LeftCube, sortedKernel f (unitClock p.1.1) (unitClock p.1.2) (unitClock p.2)
        ∂((panPairLaw r).prod (panPairLaw r)).prod (panPairLaw r) := by
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  rw [pan_integral_eq_selected r hr hn ht _ (clockFeature_continuous f).stronglyMeasurable,
    integral_sorted_eq_selected _ f unitClock unitClock_antitone
      (selected_clock_integrable _ f)]
  rfl

end Rhone.Statistics.PanIIDRepresentation
