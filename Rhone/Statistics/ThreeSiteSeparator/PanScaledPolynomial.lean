/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PanIIDRepresentation.PolynomialLaw

/-! # The pan iid representation with an arbitrary positive clock scale -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open AtomicRank AtomicSmoothing Algebra.Identifiability MarkovChain.Identifiability Identifiability
    PanIIDRepresentation

def scaledClock (a t : ℝ) : ℝ := unitClock (a*t)

def scaledFeature (a : ℝ) (f : Coefficients) (p : ℝ × ℝ) : ℝ :=
  value f (scaledClock a p.1) (scaledClock a p.2)

lemma scaledClock_continuous (a : ℝ) : Continuous (scaledClock a) := by
  exact unitClock_lipschitz.continuous.comp (continuous_const.mul continuous_id)

lemma scaledClock_antitone {a : ℝ} (ha : 0 ≤ a) : Antitone (scaledClock a) := by
  intro s t hst
  exact unitClock_antitone (mul_le_mul_of_nonneg_left hst ha)

lemma scaledFeature_continuous (a : ℝ) (f : Coefficients) : Continuous (scaledFeature a f) :=
  (value_continuous f).comp
    (((scaledClock_continuous a).comp continuous_fst).prodMk
      ((scaledClock_continuous a).comp continuous_snd))

lemma scaledFeature_bound (a : ℝ) (f : Coefficients) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p, ‖scaledFeature a f p‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := clockFeature_bound f
  refine ⟨M, hM, ?_⟩
  intro p
  exact hb (a*p.1, a*p.2)

lemma selected_scaled_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℝ) (f : Coefficients) :
    Integrable (fun p : LeftCube =>
      selectedKernel (fun x y => scaledFeature a f (x,y)) p.1.1 p.1.2 p.2)
      ((μ.prod μ).prod μ) := by
  obtain ⟨M, hM, hb⟩ := scaledFeature_bound a f
  have hm : Measurable (fun p : LeftCube =>
      selectedKernel (fun x y => scaledFeature a f (x,y)) p.1.1 p.1.2 p.2) := by
    unfold selectedKernel
    exact ((scaledFeature_continuous a f).measurable.comp (by fun_prop)).ite
      (by measurability) measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable M
  apply Filter.Eventually.of_forall
  intro p
  unfold selectedKernel
  split_ifs
  · exact hb _
  · simpa only [norm_zero] using hM

theorem pan_scaled_polynomial_iid (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {a : ℝ} (ha : 0 ≤ a) (f : Coefficients) :
    (∫ p, scaledFeature a f p ∂PanThreeSample.law r) =
      ∫ p : LeftCube, sortedKernel f (scaledClock a p.1.1)
        (scaledClock a p.1.2) (scaledClock a p.2)
        ∂((panPairLaw r).prod (panPairLaw r)).prod (panPairLaw r) := by
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hn ht
  rw [pan_integral_eq_selected r hr hn ht _ (scaledFeature_continuous a f).stronglyMeasurable,
    integral_sorted_eq_selected _ f (scaledClock a) (scaledClock_antitone ha)
      (selected_scaled_integrable _ a f)]
  rfl

end Rhone.Statistics.ThreeSiteSeparator
