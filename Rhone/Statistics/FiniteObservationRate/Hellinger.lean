/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.FiniteProduct
public import Mathlib.Analysis.Real.Sqrt

/-! # Finite Hellinger algebra for testing lower bounds -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.FiniteObservationRate
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

def affinity (P Q : Law X) : ℝ := ∑ x, Real.sqrt (P.mass x) * Real.sqrt (Q.mass x)

def hellingerSq (P Q : Law X) : ℝ := ∑ x, (Real.sqrt (P.mass x) - Real.sqrt (Q.mass x)) ^ 2

theorem hellinger_nonneg (P Q : Law X) : 0 ≤ hellingerSq P Q := by
  unfold hellingerSq
  exact Finset.sum_nonneg fun x _ => sq_nonneg _

theorem affinity_nonneg (P Q : Law X) : 0 ≤ affinity P Q := by
  unfold affinity
  exact Finset.sum_nonneg fun x _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem hellinger_affinity (P Q : Law X) : hellingerSq P Q = 2 - 2 * affinity P Q := by
  have he (x : X) : (Real.sqrt (P.mass x) - Real.sqrt (Q.mass x)) ^ 2 =
      P.mass x + Q.mass x - 2 * (Real.sqrt (P.mass x) * Real.sqrt (Q.mass x)) := by
    nlinarith [Real.sq_sqrt (P.nonneg x), Real.sq_sqrt (Q.nonneg x)]
  simp only [hellingerSq, he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, P.total, Q.total, affinity]
  ring

theorem affinity_le_one (P Q : Law X) : affinity P Q ≤ 1 := by
  have h := hellinger_nonneg P Q
  rw [hellinger_affinity] at h
  linarith

theorem totalVariation_sq_le_hellinger (P Q : Law X) :
    totalVariation P Q ^ 2 ≤ hellingerSq P Q := by
  have he (x : X) : |P.mass x - Q.mass x| =
      |Real.sqrt (P.mass x) - Real.sqrt (Q.mass x)| *
        (Real.sqrt (P.mass x) + Real.sqrt (Q.mass x)) := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (P.nonneg x), Real.sq_sqrt (Q.nonneg x)]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |Real.sqrt (P.mass x) - Real.sqrt (Q.mass x)|)
    (fun x => Real.sqrt (P.mass x) + Real.sqrt (Q.mass x))
  have hp (x : X) : (Real.sqrt (P.mass x) + Real.sqrt (Q.mass x)) ^ 2 =
      P.mass x + Q.mass x + 2 * (Real.sqrt (P.mass x) * Real.sqrt (Q.mass x)) := by
    nlinarith [Real.sq_sqrt (P.nonneg x), Real.sq_sqrt (Q.nonneg x)]
  simp only [← he, sq_abs, hp, Finset.sum_add_distrib, ← Finset.mul_sum,
    P.total, Q.total] at hc
  change (∑ x, |P.mass x - Q.mass x|) ^ 2 ≤ hellingerSq P Q * (1 + 1 + 2 * affinity P Q) at hc
  have hnon := hellinger_nonneg P Q
  have ha := affinity_le_one P Q
  unfold totalVariation
  nlinarith

end Rhone.Statistics.FiniteObservationRate
