/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.MeasureBridge

/-! # Source-calibrated 500-replicate rule; distinct from self-normalization -/

@[expose] public section

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget Identifiability.FinitePanelSampling
variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

def calibratedRejects (f : X → ℝ) (z : Fin 500 → X) : Prop :=
  (15 : ℝ) / 122 ≤ sampleMean f z

theorem calibrated_exponential_bound :
    2 * Real.exp (-(500 : ℝ) * (15 / 122) ^ 2 / 2) ≤ (1 : ℝ) / 20 := by
  have h := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 500 * (15 / 122) ^ 2 / 2) 9
  norm_num [Finset.sum_range_succ] at h
  have h40 : (40 : ℝ) ≤ Real.exp (500 * (15 / 122) ^ 2 / 2) := by linarith
  rw [show -(500 : ℝ) * (15 / 122) ^ 2 / 2 = -(500 * (15 / 122) ^ 2 / 2) by ring,
    Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

theorem calibrated_null_size (P : Law X) (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hmean : rejection P f = 0) :
    probability (iid P 500) (calibratedRejects f) ≤ (1 : ℝ) / 20 := by
  have ht := iid_sampleMean_abs_ge (lawMeasure P) f (by fun_prop) hf
    (by norm_num : 0 < 500) (by norm_num : (0 : ℝ) ≤ 15 / 122)
  rw [law_measure_integral, hmean] at ht
  rw [← iid_measure_probability]
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (ht.trans calibrated_exponential_bound)
  intro x hx
  change (15 : ℝ) / 122 ≤ |sampleMean f x - 0|
  simpa only [sub_zero] using hx.trans (le_abs_self _)

theorem calibrated_source_power (P : Law X) (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hmean : rejection P f = (15 : ℝ) / 61) :
    (19 : ℝ) / 20 ≤ probability (iid P 500) (calibratedRejects f) := by
  have ht := iid_sampleMean_abs_ge (lawMeasure P) f (by fun_prop) hf
    (by norm_num : 0 < 500) (by norm_num : (0 : ℝ) ≤ 15 / 122)
  rw [law_measure_integral, hmean] at ht
  have hfail : probability (iid P 500) (fun x => ¬ calibratedRejects f x) ≤ (1 : ℝ) / 20 := by
    rw [← iid_measure_probability]
    apply le_trans (measureReal_mono ?_ (measure_ne_top _ _))
      (ht.trans calibrated_exponential_bound)
    intro x hx
    change (15 : ℝ) / 122 ≤ |sampleMean f x - 15 / 61|
    have ha := neg_le_abs (sampleMean f x - 15 / 61)
    change ¬ (15 : ℝ) / 122 ≤ sampleMean f x at hx
    push Not at hx
    linarith
  rw [probability_complement] at hfail
  linarith

end Rhone.Statistics.DependentPairedTest
