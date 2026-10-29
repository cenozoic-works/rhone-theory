/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.FeatureBounds
public import Rhone.Statistics.ThreeSiteRobustness.FiniteWeights
public import Rhone.Statistics.ThreeSiteRobustness.ObservationDistance
public import Rhone.Statistics.ThreeSiteSeparator.Separation

/-! # Uniform total-variation margin between island and pan three-site pattern scores -/

@[expose] public section

open MeasureTheory Set Filter
namespace Rhone.Statistics.ThreeSiteRobustness
open DependenceBudget ThreeSiteSeparator ThreeTipSites Algebra.Identifiability
    MarkovChain.Identifiability Identifiability

noncomputable def panelFeatures {K : ℕ} : Fin 5 → Panel K 3 → ℝ :=
  ![aStat, p2Stat, p3Stat, hStat, jStat]

theorem panelFeatures_bounded {K : ℕ} (hK : 3 ≤ K) (i : Fin 5) (x : Panel K 3) :
    |panelFeatures i x| ≤ 1 := by
  have h := feature_bounds hK x
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

theorem scoreVector_rejection_panelFeatures {K : ℕ} (ρ : Measure (Panel K 3))
    [IsProbabilityMeasure ρ] :
    scoreVector (fun i => rejection (finiteLaw ρ) (panelFeatures i)) = patternScore ρ := by
  have he : ∀ f : Panel K 3 → ℝ, rejection (finiteLaw ρ) f = patternMoment ρ f := by
    intro f
    simp only [rejection, finiteLaw, patternMoment, mul_comm]
  simp only [he]
  rfl

theorem pattern_score_tv {K : ℕ} (hK : 3 ≤ K)
    (ρ σ : Measure (Panel K 3)) [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] :
    |patternScore ρ - patternScore σ| ≤ 1467240 * finiteTV ρ σ := by
  have h := score_tv_bound (finiteLaw ρ) (finiteLaw σ) panelFeatures (panelFeatures_bounded hK)
  rw [scoreVector_rejection_panelFeatures, scoreVector_rejection_panelFeatures, finite_law_tv] at h
  exact h

theorem uniform_tv_margin {K : ℕ} (hK : 3 ≤ K)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    (10464089628335504 : ℝ) / 53591027136025535 / 1467240 ≤
      finiteTV
        (law (uniformBlockRoots K 3 (by omega)) 2 (IslandThreeTimes.durationLaw 0 1 (1 / 100)))
        (law (uniformBlockRoots K 3 (by omega)) k (PanThreeSample.durationLaw r)) := by
  have hpos : 0 < K := by omega
  let : IsProbabilityMeasure (IslandThreeTimes.durationLaw 0 1 (1 / 100)) :=
    IslandThreeTimes.durationLaw_probability 0 (by norm_num) (by norm_num)
  let : IsProbabilityMeasure (PanThreeSample.durationLaw r) :=
    PanThreeSample.durationLaw_probability r hr hn ht
  let : IsProbabilityMeasure
      (law (uniformBlockRoots K 3 hpos) 2 (IslandThreeTimes.durationLaw 0 1 (1 / 100))) :=
    law_probability hpos _ (by norm_num) (IslandThreeTimes.durationLaw_nonnegative _ _ _)
  let : IsProbabilityMeasure
      (law (uniformBlockRoots K 3 hpos) k (PanThreeSample.durationLaw r)) :=
    law_probability hpos _ hk.le (PanThreeSample.durationLaw_nonnegative r)
  have h := (abs_le.mp (pattern_score_tv hK
    (law (uniformBlockRoots K 3 hpos) 2 (IslandThreeTimes.durationLaw 0 1 (1 / 100)))
    (law (uniformBlockRoots K 3 hpos) k (PanThreeSample.durationLaw r)))).2
  rw [source_pattern_score hK] at h
  have hnscore := pan_pattern_score_nonpos hK r hr hn ht hk
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1467240)).mpr
  linarith

end Rhone.Statistics.ThreeSiteRobustness
