/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplePanCutoff

/-! # The raw finite-time three-sample count law has its exact subprobability mass -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace MixedPoisson

lemma law_univ_eq (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : law a b μ univ = μ univ := by
  have hs : HasSum (mass a b μ) (μ.real univ) := by
    simpa using mass_pgf_hasSum μ hμ ha hb
      (show (1 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp)
  rw [law, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
    indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (mass_nonneg μ hμ ha hb) hs.summable, hs.tsum_eq]
  exact ENNReal.ofReal_toReal (measure_ne_top μ univ)

end MixedPoisson
namespace ThreeSamplePanCutoff

lemma countLaw_univ_eq (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ t, 0 ≤ f t) {r : ℝ} (hr : 0 ≤ r) :
    PanThreeSample.countLaw r f univ = PanThreeSample.law f univ := by
  let := law_isFinite f hf hn
  let : IsFiniteMeasure (PanThreeSample.durationLaw f) :=
    Measure.isFiniteMeasure_map (PanThreeSample.law f) PanThreeSample.toDurations
  let : IsFiniteMeasure ((PanThreeSample.durationLaw f).map ThreeSampleCounts.branches) :=
    Measure.isFiniteMeasure_map (PanThreeSample.durationLaw f) ThreeSampleCounts.branches
  rw [PanThreeSample.countLaw, ThreeSampleCounts.law,
    MixedPoisson.law_univ_eq _
      (ThreeSampleCounts.nonnegative_branch_law _ (PanThreeSample.durationLaw_nonnegative f)) hr hr,
    Measure.map_apply ThreeSampleCounts.measurable_branches MeasurableSet.univ,
    preimage_univ, PanThreeSample.durationLaw,
    Measure.map_apply PanThreeSample.measurable_toDurations MeasurableSet.univ, preimage_univ]

lemma countLaw_mass_le_one (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ t, 0 ≤ f t) {r : ℝ} (hr : 0 ≤ r) :
    PanThreeSample.countLaw r f univ ≤ 1 := by
  rw [countLaw_univ_eq f hf hn hr]
  exact law_mass_le_one f hf hn

def orderedCell (r : ℝ) (k : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  MixedPoisson.cell (r * (p.2 + 2 * p.1)) k.1 *
    MixedPoisson.cell (r * (p.2 - p.1)) k.2

lemma orderedCell_continuous (r : ℝ) (k : ℕ × ℕ) : Continuous (orderedCell r k) := by
  unfold orderedCell MixedPoisson.cell
  fun_prop

lemma orderedCell_nonneg {r : ℝ} (hr : 0 ≤ r) (k : ℕ × ℕ) {p : ℝ × ℝ}
    (hp : p ∈ upperWedge) : 0 ≤ orderedCell r k p := by
  apply mul_nonneg
  · exact MixedPoisson.cell_nonneg (mul_nonneg hr (by linarith [hp.1, hp.2])) _
  · exact MixedPoisson.cell_nonneg (mul_nonneg hr (sub_nonneg.mpr hp.2.le)) _

lemma orderedCell_le_one {r : ℝ} (hr : 0 ≤ r) (k : ℕ × ℕ) {p : ℝ × ℝ}
    (hp : p ∈ upperWedge) : orderedCell r k p ≤ 1 := by
  exact (mul_le_of_le_one_left
      (MixedPoisson.cell_nonneg (mul_nonneg hr (sub_nonneg.mpr hp.2.le)) _)
      (MixedPoisson.cell_le_one (mul_nonneg hr (by linarith [hp.1, hp.2])) _)).trans
      (MixedPoisson.cell_le_one (mul_nonneg hr (sub_nonneg.mpr hp.2.le)) _)

lemma orderedCell_integrable (f : ℝ → ℝ) [IsFiniteMeasure (PanThreeSample.law f)]
    {r : ℝ} (hr : 0 ≤ r) (k : ℕ × ℕ) :
    Integrable (orderedCell r k) (PanThreeSample.law f) := by
  apply Integrable.of_bound (orderedCell_continuous r k).aestronglyMeasurable 1
  filter_upwards [PanThreeSample.law_ordered_support f] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (orderedCell_nonneg hr k hp)]
  exact orderedCell_le_one hr k hp

lemma countLaw_real_singleton_integral (f : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) (k : ℕ × ℕ) :
    (PanThreeSample.countLaw r f).real {k} =
      ∫ p, orderedCell r k p ∂PanThreeSample.law f := by
  rw [PanThreeSample.countLaw, ThreeSampleCounts.law,
    MixedPoisson.law_real_singleton _
      (ThreeSampleCounts.nonnegative_branch_law _ (PanThreeSample.durationLaw_nonnegative f)) hr hr]
  unfold MixedPoisson.mass PanThreeSample.durationLaw
  rw [Measure.map_map ThreeSampleCounts.measurable_branches
    PanThreeSample.measurable_toDurations]
  have hm : Continuous (fun p : ℝ × ℝ =>
      MixedPoisson.cell (r * p.1) k.1 * MixedPoisson.cell (r * p.2) k.2) := by
    unfold MixedPoisson.cell
    fun_prop
  rw [integral_map (ThreeSampleCounts.measurable_branches.comp
    PanThreeSample.measurable_toDurations).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    dsimp [orderedCell, ThreeSampleCounts.branches, PanThreeSample.toDurations]
    congr 2
    ring

end ThreeSamplePanCutoff
end Rhone.Statistics.Identifiability
