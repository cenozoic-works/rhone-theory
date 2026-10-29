/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.ScoreConcentration

/-! # Fixed-N test and its Hoeffding sample budget -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
namespace Rhone.Statistics.ThreeSiteRobustness
open ThreeSiteSeparator ThreeTipSites Algebra.Identifiability MarkovChain.Identifiability
    Identifiability
open FinitePanelSampling

def sourceGap : ℝ := 10464089628335504 / 53591027136025535

def testRadius : ℝ := sourceGap / (4 * 733620)

def rejects {K N : ℕ} (x : Fin N → Panel K 3) : Prop := sourceGap / 4 < empiricalScore x

theorem source_gap_pos : 0 < sourceGap := by norm_num [sourceGap]
theorem test_radius_pos : 0 < testRadius := by
  unfold testRadius
  exact div_pos source_gap_pos (by norm_num)

theorem radius_score : 733620 * testRadius = sourceGap / 4 := by
  unfold testRadius
  ring

theorem null_test_error {K N : ℕ} (hK : 3 ≤ K)
    (ρ : Measure (Panel K 3)) [IsProbabilityMeasure ρ] (hN : 0 < N)
    (hs : patternScore ρ ≤ 0) {γ : ℝ} (hγ : 0 < γ)
    (hbudget : hoeffdingSampleBudget 5 testRadius γ ≤ (N : ℝ)) :
    (iidLaw ρ N).real {x | rejects x} ≤ γ := by
  have hb := iid_score_error_bound hK ρ hN test_radius_pos.le
  have he := hoeffding_failure_le (S := N) (by norm_num : 0 < 5) test_radius_pos hγ hbudget
  norm_num only [Nat.cast_ofNat] at he
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hb.trans he)
  intro x hx
  rw [Set.mem_ofPred_eq, radius_score]
  have ha := le_abs_self (empiricalScore x - patternScore ρ)
  change sourceGap / 4 < empiricalScore x at hx
  linarith

theorem source_test_error {K N : ℕ} (hK : 3 ≤ K)
    (ρ : Measure (Panel K 3)) [IsProbabilityMeasure ρ] (hN : 0 < N)
    (hs : patternScore ρ = sourceGap) {γ : ℝ} (hγ : 0 < γ)
    (hbudget : hoeffdingSampleBudget 5 testRadius γ ≤ (N : ℝ)) :
    (iidLaw ρ N).real {x | ¬ rejects x} ≤ γ := by
  have hb := iid_score_error_bound hK ρ hN test_radius_pos.le
  have he := hoeffding_failure_le (S := N) (by norm_num : 0 < 5) test_radius_pos hγ hbudget
  norm_num only [Nat.cast_ofNat] at he
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hb.trans he)
  intro x hx
  rw [Set.mem_ofPred_eq, radius_score, hs]
  have ha := neg_le_abs (empiricalScore x - sourceGap)
  change ¬ sourceGap / 4 < empiricalScore x at hx
  have hp := source_gap_pos
  push Not at hx
  linarith

end Rhone.Statistics.ThreeSiteRobustness
