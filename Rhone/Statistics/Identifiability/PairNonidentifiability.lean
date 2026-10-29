/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PositiveSurvival
public import Rhone.Statistics.Identifiability.JointLaw
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Exact one-pair non-identifiability by the inverse coalescence hazard -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem pairSurvival_pos (k : Nat) (c : ℝ) {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) :
    0 < survivalJet k c q 0 t :=
  finite_survival_pos _ (pairGenerator_metzler k hq) ht 0

theorem pairDensity_pos (k : Nat) {c q t : ℝ} (hc : 0 < c) (hq : 0 ≤ q) (ht : 0 ≤ t) :
    0 < densityJet k c q 0 t := by
  simp only [densityJet, flowOutput, pow_zero, Matrix.one_mul]
  simpa [MarkovChain.Identifiability.pairDensity, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      using
    mul_pos (exp_generator_diagonal_pos _ (pairGenerator_metzler k hq) ht 0) hc

noncomputable def pairHazard (k : Nat) (c q t : ℝ) : ℝ :=
  densityJet k c q 0 t / survivalJet k c q 0 t

noncomputable def pairClock (k : Nat) (c q t : ℝ) : ℝ := -Real.log (survivalJet k c q 0 t)

noncomputable def effectivePairSize (k : Nat) (c q t : ℝ) : ℝ :=
  survivalJet k c q 0 t / densityJet k c q 0 t

theorem pairHazard_pos (k : Nat) {c q t : ℝ} (hc : 0 < c) (hq : 0 ≤ q) (ht : 0 ≤ t) :
    0 < pairHazard k c q t := div_pos (pairDensity_pos k hc hq ht) (pairSurvival_pos k c hq ht)

theorem effectivePairSize_pos (k : Nat) {c q t : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (ht : 0 ≤ t) : 0 < effectivePairSize k c q t :=
  div_pos (pairSurvival_pos k c hq ht) (pairDensity_pos k hc hq ht)

theorem pair_survival_derivative (k : Nat) (c q t : ℝ) :
    HasDerivAt (survivalJet k c q 0) (-densityJet k c q 0 t) t := by
  have h := survival_hasDerivAt_exit (MarkovChain.Identifiability.pairGenerator k c q) 0 t
  rw [pair_exitRate] at h
  convert! h using 1

theorem pairClock_hasDerivAt (k : Nat) (c : ℝ) {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) :
    HasDerivAt (pairClock k c q) (pairHazard k c q t) t := by
  have h := ((pair_survival_derivative k c q t).log (pairSurvival_pos k c hq ht).ne').neg
  convert! h using 1
  simp only [pairHazard]
  ring

@[simp] theorem pairClock_zero (k : Nat) (c q : ℝ) : pairClock k c q 0 = 0 := by
  simp [pairClock, survivalJet]

theorem pairHazard_intervalIntegrable (k : Nat) (c : ℝ) {q T : ℝ}
    (hq : 0 ≤ q) (hT : 0 ≤ T) : IntervalIntegrable (pairHazard k c q) volume 0 T := by
  apply ContinuousOn.intervalIntegrable_of_Icc hT
  apply (flowOutput_continuous (MarkovChain.Identifiability.pairGenerator k c q) 0
      (MarkovChain.Identifiability.pairDensity c) 0).continuousOn.div
    (flowOutput_continuous (MarkovChain.Identifiability.pairGenerator k c q) 0
        MarkovChain.Identifiability.pairSurvival 0).continuousOn
  intro t ht
  exact (pairSurvival_pos k c hq ht.1).ne'

theorem pairClock_integral (k : Nat) (c : ℝ) {q T : ℝ}
    (hq : 0 ≤ q) (hT : 0 ≤ T) : (∫ t in 0..T, pairHazard k c q t) = pairClock k c q T := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => pairClock_hasDerivAt k c hq (by rw [uIcc_of_le hT] at ht; exact ht.1))
    (pairHazard_intervalIntegrable k c hq hT)
  simpa using h

theorem pairHazard_reconstructs_density (k : Nat) (c : ℝ) {q t : ℝ}
    (hq : 0 ≤ q) (ht : 0 ≤ t) :
    pairHazard k c q t * Real.exp (-pairClock k c q t) = densityJet k c q 0 t := by
  rw [pairHazard, pairClock, neg_neg, Real.exp_log (pairSurvival_pos k c hq ht)]
  exact div_mul_cancel₀ _ (pairSurvival_pos k c hq ht).ne'

noncomputable def panPairLaw (rate : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (rate t * Real.exp (-(∫ x in 0..t, rate x))))

theorem panPairLaw_pairHazard_eq (k : Nat) (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    panPairLaw (pairHazard k c q) = firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q)
        0 := by
  unfold panPairLaw firstExitLaw
  rw [pair_exitRate]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [pairClock_integral k c hq ht.le, pairHazard_reconstructs_density k c hq ht.le]
  rfl

theorem island_pair_exact_size_match (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ∃ rate : ℝ → ℝ, (∀ t, 0 ≤ t → 0 < rate t) ∧
      (∀ T, 0 ≤ T → IntervalIntegrable rate volume 0 T) ∧
      panPairLaw rate = firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0 ∧
      IsProbabilityMeasure (panPairLaw rate) := by
  refine ⟨pairHazard k c q, fun t ht => pairHazard_pos k hc hq.le ht,
    fun T hT => pairHazard_intervalIntegrable k c hq.le hT,
    panPairLaw_pairHazard_eq k c hq.le, ?_⟩
  rw [panPairLaw_pairHazard_eq k c hq.le]
  exact pair_firstExitLaw_probability k hc hq 0

end Rhone.Statistics.Identifiability
