/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LocalizedBetting.Shift
public import Rhone.Statistics.LocalizedBetting.Power

/-! # Exact numerical calibration; the source-table premises are stated separately -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.ConcreteBettingFeatures
open LocalizedBetting ThreeSiteRobustness ThreeSiteSeparator
open DependenceBudget DependentPairedTest

def sourceMeans : Fin 5 → ℝ :=
  ![101 / 305, 201 / 1009, 301 / 2113, 159009073 / 2588815905, 153944395 / 2854770763]

def margin : ℝ := scoreVector sourceMeans - 401520 * (1 / 100000) ^ 2

def eta : ℝ := 1 / 400000000

def logMeanBound : ℝ := 236 / 1000000000000

def logSecondBound : ℝ := 504 / 1000000000000

theorem numerical_mean_bound :
    logMeanBound ≤ eta * margin - 511 / 1000 * eta ^ 2 * (78914008 + margin ^ 2) := by
  dsimp [logMeanBound, eta, margin, scoreVector, sourceMeans, score, linearScore]
  norm_num

theorem numerical_second_bound :
    1021 / 1000 * eta ^ 2 * (78914008 + margin ^ 2) ≤ logSecondBound := by
  dsimp [logSecondBound, eta, margin, scoreVector, sourceMeans, score, linearScore]
  norm_num

variable {X : Type*} [Fintype X]

theorem source_log_bounds (P : Law X) (z : X → ℝ) (hz : rejection P z = 0)
    (hs : rejection P (fun x => z x ^ 2) ≤ 78914008)
    (hi : ∀ x, |eta * (z x + margin)| ≤ 1 / 100) :
    logMeanBound ≤ rejection P (fun x => Real.log (1 + eta * (z x + margin))) ∧
    rejection P (fun x => Real.log (1 + eta * (z x + margin)) ^ 2) ≤ logSecondBound := by
  have hsecond : rejection P (fun x => (eta * (z x + margin)) ^ 2) ≤
      eta ^ 2 * (78914008 + margin ^ 2) := by
    rw [increment_second P z eta margin hz]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg eta)
  constructor
  · have h := log_mean_lower P (fun x => eta * (z x + margin)) hi
    rw [increment_mean P z eta margin hz] at h
    have hn := numerical_mean_bound
    nlinarith
  · have h := log_second_bound P (fun x => eta * (z x + margin)) hi
    have hn := numerical_second_bound
    nlinarith

theorem budget_eighty : (3 : ℝ) < 72000000000 * logMeanBound ∧
    3 / 1250 + 72000000000 * logSecondBound /
      (72000000000 * logMeanBound - 3) ^ 2 ≤ 1 / 5 := by
  norm_num [logMeanBound, logSecondBound]

theorem budget_ninety_five : (3 : ℝ) < 250000000000 * logMeanBound ∧
    3 / 1250 + 250000000000 * logSecondBound /
      (250000000000 * logMeanBound - 3) ^ 2 ≤ 1 / 20 := by
  norm_num [logMeanBound, logSecondBound]

end Rhone.Statistics.ConcreteBettingFeatures
