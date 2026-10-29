/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeNoMigrationDensity
public import Rhone.Statistics.Identifiability.ThreeSharedComponentTesting

/-! # A common finite-time genealogy component with explicitly computable mass -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.ThreeNoMigration

def weight (k : ℕ) (c q : ℝ) : ℝ :=
  c ^ 2 / ((c + MarkovChain.Identifiability.totalMigration k q) *
      (c + 2 * MarkovChain.Identifiability.totalMigration k q))

def law (k : ℕ) (c q : ℝ) : Measure (ℝ × ℝ) := triangularDensityLaw (density k c q)

lemma weight_nonnegative (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) :
    0 ≤ weight k c q := by
  unfold weight MarkovChain.Identifiability.totalMigration
  positivity

lemma weight_mul_density (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) (p : ℝ × ℝ) :
    weight k c q * ExponentialTwoEvent.density
        (3 * (c + MarkovChain.Identifiability.totalMigration k q))
      (c + 2 * MarkovChain.Identifiability.totalMigration k q) p = density k c q p := by
  have hm : 0 ≤ MarkovChain.Identifiability.totalMigration k q :=
      by unfold MarkovChain.Identifiability.totalMigration; positivity
  have h1 : c + MarkovChain.Identifiability.totalMigration k q ≠ 0 := ne_of_gt (by linarith)
  have h2 : c + 2 * MarkovChain.Identifiability.totalMigration k q ≠ 0 := ne_of_gt (by linarith)
  unfold weight density ExponentialTwoEvent.density ExponentialTwoEvent.shiftedDensity
  simp only [sub_zero]
  field_simp [h1, h2]

lemma law_eq_scaled (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) :
    law k c q = ENNReal.ofReal (weight k c q) •
      ExponentialTwoEvent.law (3 * (c + MarkovChain.Identifiability.totalMigration k q))
          (c + 2 * MarkovChain.Identifiability.totalMigration k q) := by
  unfold law ExponentialTwoEvent.law triangularDensityLaw
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  filter_upwards [] with p
  rw [← weight_mul_density k hc hq p, ENNReal.ofReal_mul (weight_nonnegative k hc.le hq)]
  rfl

lemma law_real_univ (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) :
    (law k c q).real univ = weight k c q := by
  have hm : 0 ≤ MarkovChain.Identifiability.totalMigration k q :=
      by unfold MarkovChain.Identifiability.totalMigration; positivity
  let : IsProbabilityMeasure
      (ExponentialTwoEvent.law (3 * (c + MarkovChain.Identifiability.totalMigration k q))
          (c + 2 * MarkovChain.Identifiability.totalMigration k q)) :=
    ExponentialTwoEvent.law_probability (by positivity) (by positivity)
  rw [law_eq_scaled k hc hq]
  simp only [Measure.real, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (weight_nonnegative k hc.le hq)]

lemma law_le_island (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) :
    law k c q ≤ IslandThreeTimes.law k c q := by
  unfold law IslandThreeTimes.law triangularDensityLaw
  apply withDensity_mono
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  exact ENNReal.ofReal_le_ofReal (density_le_island k hc hq hp)

lemma law_le_pan (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) :
    law k c q ≤ PanThreeSample.law (fun _ => c) := by
  unfold law PanThreeSample.law triangularDensityLaw
  apply withDensity_mono
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  exact ENNReal.ofReal_le_ofReal (density_le_pan k hc hq hp)

lemma pan_const_probability {c : ℝ} (hc : 0 < c) :
    IsProbabilityMeasure (PanThreeSample.law (fun _ => c)) := by
  apply PanThreeSample.isProbability _ (locallyIntegrable_const c) (fun _ => hc.le)
  change Tendsto (fun t : ℝ => ∫ _ in (0 : ℝ)..t, c) atTop atTop
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm, id_eq] using
    (tendsto_id.const_mul_atTop hc)

theorem genealogy_event_bound (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    |(IslandThreeTimes.law k c q).real A - (PanThreeSample.law (fun _ => c)).real A| ≤
      1 - weight k c q := by
  let : IsProbabilityMeasure (IslandThreeTimes.law k c q) :=
    IslandThreeTimes.law_probability k hc hq
  let : IsProbabilityMeasure (PanThreeSample.law (fun _ => c)) := pan_const_probability hc
  simpa only [law_real_univ k hc hq.le] using CommonSubmeasure.event_bound _ _ _
    (law_le_island k hc.le hq.le) (law_le_pan k hc.le hq.le) hA

theorem genealogy_iid_error_sum_lower_bound (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (N : ℕ) {A : Set (Fin N → ℝ × ℝ)} (hA : MeasurableSet A) :
    (weight k c q) ^ N ≤
      (FinitePanelSampling.iidLaw (PanThreeSample.law (fun _ => c)) N).real A +
      (1 - (FinitePanelSampling.iidLaw (IslandThreeTimes.law k c q) N).real A) := by
  let : IsProbabilityMeasure (IslandThreeTimes.law k c q) :=
    IslandThreeTimes.law_probability k hc hq
  let : IsProbabilityMeasure (PanThreeSample.law (fun _ => c)) := pan_const_probability hc
  simpa only [law_real_univ k hc hq.le] using CommonSubmeasure.iid_error_sum_lower_bound _ _ _
    (law_le_pan k hc.le hq.le) (law_le_island k hc.le hq.le) N hA

theorem genealogy_iid_randomized_error_sum_lower_bound (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (N : ℕ) (f : (Fin N → ℝ × ℝ) → ℝ)
    (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (weight k c q) ^ N ≤
      (∫ x, f x ∂FinitePanelSampling.iidLaw (PanThreeSample.law (fun _ => c)) N) +
      ∫ x, (1 - f x) ∂FinitePanelSampling.iidLaw (IslandThreeTimes.law k c q) N := by
  let : IsProbabilityMeasure (IslandThreeTimes.law k c q) :=
    IslandThreeTimes.law_probability k hc hq
  let : IsProbabilityMeasure (PanThreeSample.law (fun _ => c)) := pan_const_probability hc
  simpa only [law_real_univ k hc hq.le] using
    CommonSubmeasure.iid_randomized_error_sum_lower_bound _ _ _
      (law_le_pan k hc.le hq.le) (law_le_island k hc.le hq.le) N f hf hb

end Rhone.Statistics.Identifiability.ThreeNoMigration
