/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.GenealogyLaplaceScore

/-! # Exact positive score of a constant two-island genealogy and observer -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open MarkovChain.Identifiability Identifiability ThreeTipSites

lemma source_combined_moment {m : ℝ} (hm : 0 < m) (p q r s : ℕ) :
    (∫ t, combinedKernel p q r s t ∂IslandThreeTimes.durationLaw 0 1 m) =
      (sourceMoment p q m+2*sourceMoment r s m)/3 := by
  let : IsProbabilityMeasure (IslandThreeTimes.durationLaw 0 1 m) :=
    IslandThreeTimes.durationLaw_probability 0 (by norm_num) hm
  rw [combinedKernel_integral _ (IslandThreeTimes.durationLaw_nonnegative 0 1 m)]
  unfold monomialKernel
  rw [integral_eq_sourceMoment hm, integral_eq_sourceMoment hm]

lemma genealogyScore_eq_sourceScore {m : ℝ} (hm : 0 < m) :
    genealogyScore 2 (IslandThreeTimes.durationLaw 0 1 m) = sourceScore m := by
  rw [genealogyScore_two_laplace]
  simp_rw [source_combined_moment hm]
  unfold sourceScore
  congr 1
  ring

theorem genealogyScore_source_pos :
    0 < genealogyScore 2 (IslandThreeTimes.durationLaw 0 1 (1/100)) := by
  rw [genealogyScore_eq_sourceScore (by norm_num)]
  exact sourceScore_one_hundredth_pos

theorem source_pattern_score {K : ℕ} (hK : 3 ≤ K) :
    patternScore (law (uniformBlockRoots K 3 (by omega)) 2
      (IslandThreeTimes.durationLaw 0 1 (1/100))) =
        (10464089628335504 / 53591027136025535 : ℝ) := by
  let : IsProbabilityMeasure (IslandThreeTimes.durationLaw 0 1 (1/100)) :=
    IslandThreeTimes.durationLaw_probability 0 (by norm_num) (by norm_num)
  rw [patternScore_law hK (by norm_num) (IslandThreeTimes.durationLaw_nonnegative 0 1 (1/100)),
    genealogyScore_eq_sourceScore (by norm_num), sourceScore_one_hundredth]

end Rhone.Statistics.ThreeSiteSeparator
