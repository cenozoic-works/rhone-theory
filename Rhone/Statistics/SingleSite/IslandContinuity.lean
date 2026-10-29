/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeWeakMigrationPower
public import Rhone.Statistics.Identifiability.IslandThreeFirstMarginal
public import Rhone.Statistics.SingleSiteChannel.Formula

/-! # Bounded island observations converge to unit pan as migration vanishes -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.SingleSite
open MarkovChain.Identifiability Identifiability

lemma expectation_gap_of_common_component {Ω : Type*} [MeasurableSpace Ω]
    (μ ν κ : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : κ ≤ μ) (hν : κ ≤ ν) (f : Ω → ℝ) (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 1 - κ.real univ := by
  have h1 := CommonSubmeasure.randomized_error_sum_lower_bound μ ν κ hμ hν f hf hb
  have h2 := CommonSubmeasure.randomized_error_sum_lower_bound ν μ κ hν hμ f hf hb
  have hc (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      (∫ x, 1 - f x ∂ρ) = 1 - ∫ x, f x ∂ρ := by
    rw [integral_sub (integrable_const 1) (CommonSubmeasure.unit_interval_integrable ρ f hf hb)]
    simp
  rw [hc ν] at h1
  rw [hc μ] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma island_bounded_expectation_tendsto (n : ℕ) (f : (ℝ × ℝ) → ℝ)
    (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    Tendsto (fun q => ∫ x, f x ∂IslandThreeTimes.law n 1 q) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, f x ∂PanThreeSample.law (fun _ => 1))) := by
  have ht : Tendsto (fun q => 1 - ThreeNoMigration.weight n 1 q)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hw := ThreeNoMigration.weight_continuousAt_zero n (by norm_num : (0 : ℝ) < 1)
    have h := ((hw.tendsto).const_sub 1).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa only [ThreeNoMigration.weight_zero n (by norm_num : (0 : ℝ) < 1), sub_self] using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hnear := ht.eventually (Iio_mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hnear] with q hq he
  have hqp : (0 : ℝ) < q := hq
  let : IsProbabilityMeasure (IslandThreeTimes.law n 1 q) :=
    IslandThreeTimes.law_probability n (by norm_num) hqp
  let : IsProbabilityMeasure (PanThreeSample.law (fun _ => (1 : ℝ))) :=
    ThreeNoMigration.pan_const_probability (by norm_num)
  have h := expectation_gap_of_common_component
    (IslandThreeTimes.law n 1 q) (PanThreeSample.law (fun _ => 1))
    (ThreeNoMigration.law n 1 q)
    (ThreeNoMigration.law_le_island n (by norm_num) hqp.le)
    (ThreeNoMigration.law_le_pan n (by norm_num) hqp.le) f hf hb
  rw [ThreeNoMigration.law_real_univ n (by norm_num) hqp.le] at h
  rw [Real.dist_eq]
  exact h.trans_lt he

def clipDurations (p : ℝ × ℝ) : ℝ × ℝ := (max 0 p.1, max 0 (p.2 - p.1))

lemma clipDurations_measurable : Measurable clipDurations := by
  unfold clipDurations
  fun_prop

lemma clipDurations_nonnegative (p : ℝ × ℝ) :
    0 ≤ (clipDurations p).1 ∧ 0 ≤ (clipDurations p).2 :=
  ⟨le_max_left _ _, le_max_left _ _⟩

lemma clipDurations_eq {p : ℝ × ℝ} (hp : p ∈ upperWedge) :
    clipDurations p = PanThreeSample.toDurations p := by
  simp only [clipDurations, PanThreeSample.toDurations,
    max_eq_right hp.1.le, max_eq_right (sub_nonneg.mpr hp.2.le)]

lemma clipped_integral_eq (μ : Measure (ℝ × ℝ))
    (hμ : ∀ᵐ p ∂μ, p ∈ upperWedge) (f : (ℝ × ℝ) → ℝ) (hf : Measurable f) :
    (∫ p, f (clipDurations p) ∂μ) = ∫ p, f p ∂μ.map PanThreeSample.toDurations := by
  rw [integral_map PanThreeSample.measurable_toDurations.aemeasurable hf.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hμ] with p hp
  rw [clipDurations_eq hp]

lemma pan_ordered_ae (rate : ℝ → ℝ) :
    ∀ᵐ p ∂PanThreeSample.law rate, p ∈ upperWedge :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem upperWedge_open.measurableSet)

theorem island_duration_expectation_tendsto (n : ℕ) (f : (ℝ × ℝ) → ℝ)
    (hf : Measurable f)
    (hb : ∀ p : ℝ × ℝ, 0 ≤ p.1 ∧ 0 ≤ p.2 → 0 ≤ f p ∧ f p ≤ 1) :
    Tendsto (fun q => ∫ p, f p ∂IslandThreeTimes.durationLaw n 1 q) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ p, f p ∂PanThreeSample.durationLaw (fun _ => 1))) := by
  have h := island_bounded_expectation_tendsto n (fun p => f (clipDurations p))
    (hf.comp clipDurations_measurable) (fun p => hb _ (clipDurations_nonnegative p))
  rw [clipped_integral_eq _ (pan_ordered_ae _) f hf] at h
  change Tendsto _ _ (𝓝 (∫ p, f p ∂PanThreeSample.durationLaw (fun _ => 1))) at h
  apply h.congr'
  filter_upwards [] with q
  have he := clipped_integral_eq (IslandThreeTimes.law n 1 q)
    (IslandThreeTimes.law_ordered_ae n 1 q) f hf
  exact he

end Rhone.Statistics.SingleSite
