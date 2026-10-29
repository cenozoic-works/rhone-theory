/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.UniformTest

/-! # Pan-null and island-source iid error endpoints -/

@[expose] public section

open MeasureTheory Set Filter
namespace Rhone.Statistics.ThreeSiteRobustness
open ThreeSiteSeparator ThreeTipSites Algebra.Identifiability MarkovChain.Identifiability
    Identifiability
open FinitePanelSampling

theorem uniform_pan_error {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k)
    {γ : ℝ} (hγ : 0 < γ)
    (hbudget : hoeffdingSampleBudget 5 testRadius γ ≤ (N : ℝ)) :
    (iidLaw (law (uniformBlockRoots K 3 (by omega)) k
      (PanThreeSample.durationLaw r)) N).real {x | rejects x} ≤ γ := by
  let : IsProbabilityMeasure (PanThreeSample.durationLaw r) :=
    PanThreeSample.durationLaw_probability r hr hn ht
  let : IsProbabilityMeasure
      (law (uniformBlockRoots K 3 (by omega)) k (PanThreeSample.durationLaw r)) :=
    law_probability (by omega) _ hk.le (PanThreeSample.durationLaw_nonnegative r)
  exact null_test_error hK _ hN (pan_pattern_score_nonpos hK r hr hn ht hk) hγ hbudget

theorem source_error {K N : ℕ} (hK : 3 ≤ K) (hN : 0 < N)
    {γ : ℝ} (hγ : 0 < γ)
    (hbudget : hoeffdingSampleBudget 5 testRadius γ ≤ (N : ℝ)) :
    (iidLaw (law (uniformBlockRoots K 3 (by omega)) 2
      (IslandThreeTimes.durationLaw 0 1 (1 / 100))) N).real {x | ¬ rejects x} ≤ γ := by
  let : IsProbabilityMeasure (IslandThreeTimes.durationLaw 0 1 (1 / 100)) :=
    IslandThreeTimes.durationLaw_probability 0 (by norm_num) (by norm_num)
  let : IsProbabilityMeasure
      (law (uniformBlockRoots K 3 (by omega)) 2
        (IslandThreeTimes.durationLaw 0 1 (1 / 100))) :=
    law_probability (by omega) _ (by norm_num)
      (IslandThreeTimes.durationLaw_nonnegative _ _ _)
  exact source_test_error hK _ hN (source_pattern_score hK) hγ hbudget

end Rhone.Statistics.ThreeSiteRobustness
