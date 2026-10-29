/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.ScoreDifference
public import Mathlib.Tactic.FinCases

/-! # The score Lipschitz constant 733620 -/

@[expose] public section

namespace Rhone.Statistics.ThreeSiteRobustness

noncomputable def coefficientBound : Fin 5 → ℝ := ![208620, 226380, 96180, 99540, 102900]

theorem coefficient_bound {v w : Fin 5 → ℝ}
    (hv : ∀ i, |v i| ≤ 1) (hw : ∀ i, |w i| ≤ 1) (i : Fin 5) :
    |coefficient v w i| ≤ coefficientBound i := by
  have hv0 := abs_le.mp (hv 0)
  have hv1 := abs_le.mp (hv 1)
  have hv2 := abs_le.mp (hv 2)
  have hw0 := abs_le.mp (hw 0)
  have hw1 := abs_le.mp (hw 1)
  fin_cases i <;> norm_num [coefficient, coefficientBound]
  all_goals apply abs_le.mpr; constructor <;> linarith

theorem score_lipschitz {v w : Fin 5 → ℝ} {ε : ℝ}
    (hv : ∀ i, |v i| ≤ 1) (hw : ∀ i, |w i| ≤ 1)
    (hclose : ∀ i, |v i - w i| ≤ ε) :
    |scoreVector v - scoreVector w| ≤ 733620*ε := by
  have he : 0 ≤ ε := (abs_nonneg _).trans (hclose 0)
  rw [score_difference]
  calc
    |∑ i, (v i - w i)*coefficient v w i| ≤ ∑ i, |(v i - w i)*coefficient v w i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε*coefficientBound i := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hclose i) (coefficient_bound hv hw i) (abs_nonneg _) he
    _ = 733620*ε := by simp [coefficientBound, Fin.sum_univ_succ]; ring

end Rhone.Statistics.ThreeSiteRobustness
