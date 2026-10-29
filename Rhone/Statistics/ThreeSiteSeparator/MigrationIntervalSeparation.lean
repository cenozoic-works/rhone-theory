/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SmallMigrationScore
public import Rhone.Statistics.ThreeSiteSeparator.Separation

/-! # The same three-site witness separates a whole weak-migration interval -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open Algebra.Identifiability MarkovChain.Identifiability Identifiability ThreeTipSites

lemma source_pattern_score_general {K : ℕ} (hK : 3 ≤ K)
    {m : ℝ} (hm : 0 < m) :
    patternScore (law (uniformBlockRoots K 3 (by omega)) 2
      (IslandThreeTimes.durationLaw 0 1 m)) = sourceScore m := by
  let : IsProbabilityMeasure (IslandThreeTimes.durationLaw 0 1 m) :=
    IslandThreeTimes.durationLaw_probability 0 (by norm_num) hm
  rw [patternScore_law hK (by norm_num) (IslandThreeTimes.durationLaw_nonnegative 0 1 m),
    genealogyScore_eq_sourceScore hm]

theorem weak_migration_three_site_separation {K : ℕ} (hK : 3 ≤ K)
    {m : ℝ} (hm : 0 < m) (hsmall : m ≤ 1 / 1000)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    law (uniformBlockRoots K 3 (by omega)) 2 (IslandThreeTimes.durationLaw 0 1 m) ≠
      law (uniformBlockRoots K 3 (by omega)) k (PanThreeSample.durationLaw r) := by
  intro he
  have hneg := pan_pattern_score_nonpos hK r hr hn ht hk
  rw [← he, source_pattern_score_general hK hm] at hneg
  exact (not_lt_of_ge hneg) (sourceScore_small_positive hm hsmall)

end Rhone.Statistics.ThreeSiteSeparator
