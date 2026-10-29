/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.PanScoreBound
public import Rhone.Statistics.ThreeSiteSeparator.SourceScore

/-! # An explicit finite-pattern separator: three samples, three linked sites -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open Algebra.Identifiability MarkovChain.Identifiability Identifiability ThreeTipSites

theorem pan_pattern_score_nonpos {K : ℕ} (hK : 3 ≤ K)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    patternScore (law (uniformBlockRoots K 3 (by omega)) k (PanThreeSample.durationLaw r)) ≤ 0 := by
  let : IsProbabilityMeasure (PanThreeSample.durationLaw r) :=
    PanThreeSample.durationLaw_probability r hr hn ht
  rw [patternScore_law hK hk.le (PanThreeSample.durationLaw_nonnegative r)]
  exact pan_genealogy_score_nonpos r hr hn ht hk

theorem three_site_separation {K : ℕ} (hK : 3 ≤ K)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    law (uniformBlockRoots K 3 (by omega)) 2 (IslandThreeTimes.durationLaw 0 1 (1/100)) ≠
      law (uniformBlockRoots K 3 (by omega)) k (PanThreeSample.durationLaw r) := by
  intro he
  have hneg := pan_pattern_score_nonpos hK r hr hn ht hk
  rw [← he, source_pattern_score hK] at hneg
  norm_num at hneg

end Rhone.Statistics.ThreeSiteSeparator
