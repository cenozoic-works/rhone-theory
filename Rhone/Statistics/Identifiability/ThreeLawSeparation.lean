/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeJets
public import Rhone.Statistics.Identifiability.PanClockCDF

/-! # Pair times plus the three-sample first-merger law break the tie -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

theorem pairGenerator_rows_nonpos (k : Nat) {c q : ℝ} (hc : 0 ≤ c) (i : Fin 2) :
    (∑ j, MarkovChain.Identifiability.pairGenerator k c q i j) ≤ 0 := by
  have h := congrFun (pair_exitRate k c q) i
  simp only [exitRate, Pi.neg_apply, Matrix.mulVec, dotProduct, mul_one] at h
  have hp := pairDensity_nonneg hc i
  linarith

theorem pairLaw_survival_CDF (k : Nat) {c q T : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hT : 0 ≤ T) :
    1 - (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0).real (Ioc 0 T) =
        survivalJet k c q 0 T := by
  rw [firstExitLaw_real_Ioc _ (pairGenerator_metzler k hq) (pairGenerator_rows_nonpos k hc) 0 hT]
  change 1 - (1 - survivalJet k c q 0 T) = survivalJet k c q 0 T
  ring

theorem threeLaw_survival_CDF (k : Nat) {c q T : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hT : 0 ≤ T) :
    1 - (firstExitLaw (threeGenerator k c q) 0).real (Ioc 0 T) = threeSurvivalJet k c q 0 T := by
  rw [firstExitLaw_real_Ioc _ (threeGenerator_metzler k c hq)
    (threeGenerator_rows_nonpos k hc) 0 hT]
  change 1 - (1 - threeSurvivalJet k c q 0 T) = threeSurvivalJet k c q 0 T
  ring

noncomputable def threeSampleCDFStatistic (pairLaw firstMergerLaw : Measure ℝ) (t : ℝ) : ℝ :=
  (1 - firstMergerLaw.real (Ioc 0 t)) - (1 - pairLaw.real (Ioc 0 t))^3

theorem pan_threeSampleCDFStatistic_zero (rate : ℝ → ℝ)
    (hRate : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t) {T : ℝ} (hT : 0 ≤ T) :
    threeSampleCDFStatistic (panPairLaw rate) (panPairLaw (fun t => 3*rate t)) T = 0 := by
  unfold threeSampleCDFStatistic
  rw [pan_pair_three_survival_identity rate hRate hn hT]
  ring

theorem island_threeSampleCDFStatistic_eq (k : Nat) {c q T : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hT : 0 ≤ T) :
    threeSampleCDFStatistic (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0)
      (firstExitLaw (threeGenerator k c q) 0) T = threeWitness k c q T := by
  rw [threeSampleCDFStatistic, pairLaw_survival_CDF k hc hq hT, threeLaw_survival_CDF k hc hq hT]
  rfl

theorem island_threeSampleCDFStatistic_nonzero (k : Nat) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) :
    ∃ T ∈ Icc (0 : ℝ) 1,
      threeSampleCDFStatistic (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0)
        (firstExitLaw (threeGenerator k c q) 0) T ≠ 0 := by
  by_contra hn
  push Not at hn
  apply threeWitness_not_zero_on_unit_interval k hc hq
  intro T hT
  rw [← island_threeSampleCDFStatistic_eq k hc.le hq.le hT.1]
  exact hn T hT

theorem pair_and_three_no_common_size_match (k : Nat) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) :
    ¬ ∃ rate : ℝ → ℝ, LocallyIntegrable rate volume ∧ (∀ t, 0 ≤ rate t) ∧
      panPairLaw rate = firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0 ∧
      panPairLaw (fun t => 3*rate t) = firstExitLaw (threeGenerator k c q) 0 := by
  rintro ⟨rate,hRate,hn,hpair,hthree⟩
  obtain ⟨T,hT,hne⟩ := island_threeSampleCDFStatistic_nonzero k hc hq
  apply hne
  rw [← hpair, ← hthree]
  exact pan_threeSampleCDFStatistic_zero rate hRate hn hT.1

end Rhone.Statistics.Identifiability
