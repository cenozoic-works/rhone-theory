/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PairObservationChannel.Law

/-! # Identity-channel specialization for the clean observation model -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.PairObservationChannel

noncomputable def identityChannel (K : ℕ) (hK : 0 < K) : Channel K (Fin K) where
  positive := hK
  row := fun i y => if i = y then 1 else 0
  nonneg := by intro i y; split_ifs <;> norm_num
  normalized := by intro i; simp

theorem identity_column_mean (K : ℕ) (hK : 0 < K) (y : Fin K) :
    columnMean (identityChannel K hK) y = 1 / (K : ℝ) := by
  simp [columnMean, identityChannel]

theorem identity_shared_mass (K : ℕ) (hK : 0 < K) (x y : Fin K) :
    sharedMass (identityChannel K hK) x y = if x = y then 1 / (K : ℝ) else 0 := by
  unfold sharedMass identityChannel
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  split_ifs <;> simp_all

theorem identity_baseline (K : ℕ) (hK : 0 < K) : baseline (identityChannel K hK) = 1 / (K : ℝ) := by
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  unfold baseline
  simp only [identity_column_mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

theorem identity_variance (K : ℕ) (hK : 0 < K) :
    retainedVariance (identityChannel K hK) = 1 - 1 / (K : ℝ) := by
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  rw [retained_variance_formula, identity_baseline]
  simp [identity_shared_mass, hk]

theorem identity_agreement (K : ℕ) (hK : 0 < K) (ℓ : ℝ) :
    agreement (identityChannel K hK) ℓ = 1 / (K : ℝ) + (1 - 1 / (K : ℝ)) * ℓ := by
  rw [agreement_formula, identity_baseline, identity_variance]

end Rhone.Statistics.PairObservationChannel
