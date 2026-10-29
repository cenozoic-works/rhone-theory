/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SevenSiteSeparator.Score
public import Rhone.Statistics.ThreeSiteSeparator.Separation

/-! # Seven-site separator reusing the score certificate -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.SevenSiteSeparator
open ThreeSiteSeparator Algebra.Identifiability MarkovChain.Identifiability Identifiability
    ThreeTipSites

theorem source_seven_score {K : ℕ} (hK : 2 ≤ K) :
    sevenScore (law (uniformBlockRoots K 7 (by omega)) 1
      (IslandThreeTimes.durationLaw 0 1 (1 / 100))) =
        (10464089628335504 / 53591027136025535 : ℝ) := by
  let : IsProbabilityMeasure (IslandThreeTimes.durationLaw 0 1 (1 / 100)) :=
    IslandThreeTimes.durationLaw_probability 0 (by norm_num) (by norm_num)
  rw [sevenScore_law hK (by norm_num)
    (IslandThreeTimes.durationLaw_nonnegative 0 1 (1 / 100))]
  norm_num only [mul_one]
  rw [genealogyScore_eq_sourceScore (by norm_num), sourceScore_one_hundredth]

theorem pan_seven_score_nonpos {K : ℕ} (hK : 2 ≤ K)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    sevenScore (law (uniformBlockRoots K 7 (by omega)) k
      (PanThreeSample.durationLaw r)) ≤ 0 := by
  let : IsProbabilityMeasure (PanThreeSample.durationLaw r) :=
    PanThreeSample.durationLaw_probability r hr hn ht
  rw [sevenScore_law hK hk.le (PanThreeSample.durationLaw_nonnegative r)]
  exact pan_genealogy_score_nonpos r hr hn ht (by positivity)

theorem seven_site_separation {K : ℕ} (hK : 2 ≤ K)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    law (uniformBlockRoots K 7 (by omega)) 1 (IslandThreeTimes.durationLaw 0 1 (1 / 100)) ≠
      law (uniformBlockRoots K 7 (by omega)) k (PanThreeSample.durationLaw r) := by
  intro he
  have hneg := pan_seven_score_nonpos hK r hr hn ht hk
  rw [← he, source_seven_score hK] at hneg
  norm_num at hneg

end Rhone.Statistics.SevenSiteSeparator
