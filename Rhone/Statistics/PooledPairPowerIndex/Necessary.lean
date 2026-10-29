/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PooledPairPowerIndex.Pooled

/-! # Necessary paired-sample budget against the pooled comparison law -/

@[expose] public section

namespace Rhone.Statistics.PooledPairPowerIndex
open DependenceBudget DependentPairedTest LinkedAgreementPower
open FiniteObservationRate
variable {X : Type*} [Fintype X]

theorem pooled_necessary_bound (P Q : Law X) (N : ℕ)
    (φ : (Fin N → X × X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hadv : δ ≤ rejection (iid (independentPair P Q) N) φ -
      rejection (iid (independentPair (pooledLaw P Q) (pooledLaw P Q)) N) φ) :
    δ ^ 2 / (2 * pooledIndex P Q) ≤ (N : ℝ) := by
  have ht := pooled_index_nonneg P Q
  by_cases hz : pooledIndex P Q = 0
  · simp [hz]
  · have hpos : 0 < pooledIndex P Q := lt_of_le_of_ne ht (Ne.symm hz)
    have hd := rejection_difference_le (iid (independentPair P Q) N)
      (iid (independentPair (pooledLaw P Q) (pooledLaw P Q)) N) φ hφ
    have hdtv := hadv.trans ((le_abs_self _).trans hd)
    have hs := mul_self_le_mul_self hδ hdtv
    have hi := iid_tv_sq_le (independentPair P Q)
      (independentPair (pooledLaw P Q) (pooledLaw P Q)) N
    have hh := mul_le_mul_of_nonneg_left (pooled_joint_hellinger_le P Q)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * pooledIndex P Q)).mpr
    nlinarith

theorem necessary_ninety_five_five (P Q : Law X) (N : ℕ)
    (φ : (Fin N → X × X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hsize : rejection (iid (independentPair (pooledLaw P Q) (pooledLaw P Q)) N) φ ≤
      (1 : ℝ) / 20)
    (hpower : (19 : ℝ) / 20 ≤ rejection (iid (independentPair P Q) N) φ) :
    (81 : ℝ) / 100 / (2 * pooledIndex P Q) ≤ (N : ℝ) := by
  have h := pooled_necessary_bound P Q N φ hφ (by norm_num : (0 : ℝ) ≤ 9 / 10)
    (by linarith)
  norm_num at h ⊢
  exact h

end Rhone.Statistics.PooledPairPowerIndex
