/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PooledPairPowerIndex.Index
public import Rhone.Statistics.FiniteObservationRate.Testing
public import Rhone.Statistics.LinkedAgreementPower.BinaryTesting

/-! # Pooled comparison law and Hellinger bounds -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.PooledPairPowerIndex
open DependenceBudget DependentPairedTest LinkedAgreementPower
open FiniteObservationRate
variable {X : Type*} [Fintype X]

def pooledLaw (P Q : Law X) : Law X where
  mass := fun x => (P.mass x + Q.mass x) / 2
  nonneg := fun x => div_nonneg (add_nonneg (P.nonneg x) (Q.nonneg x)) (by norm_num)
  total := by rw [← Finset.sum_div, Finset.sum_add_distrib, P.total, Q.total]; norm_num

theorem pooled_law_comm (P Q : Law X) : pooledLaw P Q = pooledLaw Q P := by
  apply LinkedPairMoments.finite_law_ext
  intro x
  simp only [pooledLaw, add_comm]

theorem pooled_index_comm (P Q : Law X) : pooledIndex P Q = pooledIndex Q P := by
  unfold pooledIndex categoryIndex
  apply Finset.sum_congr rfl
  intro x _
  rw [add_comm (P.mass x)]
  congr 1
  ring

theorem hellinger_pooled_le (P Q : Law X) : hellingerSq P (pooledLaw P Q) ≤ pooledIndex P Q := by
  unfold hellingerSq pooledIndex
  apply Finset.sum_le_sum
  intro x _
  have hp := P.nonneg x
  have hq := Q.nonneg x
  by_cases hz : P.mass x + Q.mass x = 0
  · have hp0 : P.mass x = 0 := by linarith
    have hq0 : Q.mass x = 0 := by linarith
    simp [pooledLaw, categoryIndex, hp0, hq0]
  · have hsum : 0 < P.mass x + Q.mass x := lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hz)
    have h := sqrt_difference_sq_le hp
      (show (0 : ℝ) < (P.mass x + Q.mass x) / 2 by positivity)
    change (Real.sqrt (P.mass x) - Real.sqrt ((P.mass x + Q.mass x) / 2)) ^ 2 ≤ _
    apply h.trans_eq
    unfold categoryIndex
    field_simp
    ring

theorem affinity_independent_pair (P Q R S : Law X) :
    affinity (independentPair P Q) (independentPair R S) = affinity P R * affinity Q S := by
  have he (x y : X) :
      Real.sqrt (P.mass x * Q.mass y) * Real.sqrt (R.mass x * S.mass y) =
        (Real.sqrt (P.mass x) * Real.sqrt (R.mass x)) *
          (Real.sqrt (Q.mass y) * Real.sqrt (S.mass y)) := by
    rw [Real.sqrt_mul (P.nonneg x), Real.sqrt_mul (R.nonneg x)]
    ring
  simp only [affinity, independentPair, Fintype.sum_prod_type, he,
    ← Finset.mul_sum, ← Finset.sum_mul]

theorem hellinger_independent_pair_le (P Q R S : Law X) :
    hellingerSq (independentPair P Q) (independentPair R S) ≤
      hellingerSq P R + hellingerSq Q S := by
  rw [hellinger_affinity, affinity_independent_pair, hellinger_affinity, hellinger_affinity]
  have h := mul_nonneg (sub_nonneg.mpr (affinity_le_one P R))
    (sub_nonneg.mpr (affinity_le_one Q S))
  nlinarith

theorem pooled_joint_hellinger_le (P Q : Law X) :
    hellingerSq (independentPair P Q) (independentPair (pooledLaw P Q) (pooledLaw P Q)) ≤
      2 * pooledIndex P Q := by
  have h1 := hellinger_pooled_le P Q
  have h2 := hellinger_pooled_le Q P
  rw [pooled_law_comm Q P, pooled_index_comm Q P] at h2
  exact (hellinger_independent_pair_le _ _ _ _).trans (by linarith)

end Rhone.Statistics.PooledPairPowerIndex
