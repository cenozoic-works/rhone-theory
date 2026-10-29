/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcreteBettingFeatures.NullBridge
public import Rhone.Statistics.ConcreteBettingFeatures.SourceBridge
public import Rhone.Statistics.LocalizedBetting.Testing

/-! # The prespecified concrete test on whole-block iid laws -/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Rhone.Statistics.ConcreteBettingFeatures
open LocalizedBetting ThreeTipSites ThreeSiteSeparator Algebra.Identifiability
    MarkovChain.Identifiability Identifiability
open DependenceBudget DependentPairedTest FinitePanelSampling

def concreteRejects {N : ℕ} (z : Fin N → Panel 4 3) : Prop :=
  LocalizedBetting.rejects sourceMeans observedFeature eta (1 / 100000) z

theorem factor_positive (x : Panel 4 3) :
    0 < factor sourceMeans observedFeature eta (1 / 100000) x := by
  have h := (abs_le.mp (source_increment_bound x)).1
  change 0 < 1 + eta * (sourceContrast x + margin)
  linarith

theorem concrete_uniform_pan_size (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {k : ℝ} (hk : 0 < k) {N : ℕ} (hN : 72000000000 ≤ N) :
    (iidLaw (law (uniformBlockRoots 4 3 (by norm_num)) k (PanThreeSample.durationLaw r)) N).real
      {z | concreteRejects z} ≤ (1 : ℝ) / 20 := by
  let := PanThreeSample.durationLaw_probability r hr hn ht
  rw [← observed_law_measure k (PanThreeSample.durationLaw r) hk.le
    (pan_nonnegative r), iid_measure_probability]
  exact uniform_null_size _ sourceMeans observedFeature observed_feature_bounds
    (by norm_num [eta]) (fun x => (factor_positive x).le)
    (pan_score_nonpositive r hr hn ht hk) hN

theorem source_localization_error {N : ℕ} (hN : 72000000000 ≤ N) :
    probability (iid sourceLaw N)
      (fun z => ¬ localizes sourceMeans observedFeature (1 / 100000) z) ≤ (3 : ℝ) / 1250 := by
  have hsub : ∀ z : Fin N → Panel 4 3,
      ¬ localizes sourceMeans observedFeature (1 / 100000) z →
      ∃ i : Fin 3, (1 / 100000 : ℝ) ≤
        |sampleMean (observedFeature (i.castLE (by decide))) z -
          rejection sourceLaw (observedFeature (i.castLE (by decide)))| := by
    intro z hz
    unfold localizes at hz
    push Not at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, by rw [source_feature_means]; exact hi.le⟩
  have h := range_four_thirds_concentration sourceLaw
    (fun i : Fin 3 => observedFeature (i.castLE (by decide)))
    (fun i x => observed_feature_bounds _ x) (show 0 < N by omega)
    (by norm_num : (0 : ℝ) ≤ 1 / 100000)
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, mul_one] at h
  have hb := localization_budget hN
  norm_num only [one_div, inv_pow, Nat.cast_ofNat, OfNat.ofNat, pow_succ, pow_zero] at hb
  exact ((probability_mono _ hsub).trans h).trans (by norm_num at hb ⊢; exact hb)

theorem source_fixed_power {N : ℕ} (hN : 72000000000 ≤ N)
    (hm : 3 < N * logMeanBound) :
    1 - 3 / 1250 - N * logSecondBound / (N * logMeanBound - 3) ^ 2 ≤
      probability (iid sourceLaw N) concreteRejects := by
  have hlog := source_log_bounds sourceLaw sourceContrast source_contrast_centered
    source_contrast_second source_increment_bound
  exact localized_power sourceLaw N (factor sourceMeans observedFeature eta (1 / 100000))
    (localizes sourceMeans observedFeature (1 / 100000)) factor_positive hlog.1 hlog.2 hm
    (source_localization_error hN)

theorem concrete_source_power_eighty :
    (4 : ℝ) / 5 ≤ (iidLaw
      (TwoIslandSpatial.spatialSequenceLaw (uniformBlockRoots 4 3 (by norm_num))
        2 1 (1 / 100)) 72000000000).real {z | concreteRejects z} := by
  rw [← source_spatial_observer, iid_measure_probability]
  have h := source_fixed_power (le_refl 72000000000) budget_eighty.1
  have hb := budget_eighty.2
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem concrete_source_power_ninety_five :
    (19 : ℝ) / 20 ≤ (iidLaw
      (TwoIslandSpatial.spatialSequenceLaw (uniformBlockRoots 4 3 (by norm_num))
        2 1 (1 / 100)) 250000000000).real {z | concreteRejects z} := by
  rw [← source_spatial_observer, iid_measure_probability]
  have h := source_fixed_power (by norm_num : 72000000000 ≤ 250000000000) budget_ninety_five.1
  have hb := budget_ninety_five.2
  norm_num only [Nat.cast_ofNat] at h
  linarith

end Rhone.Statistics.ConcreteBettingFeatures
