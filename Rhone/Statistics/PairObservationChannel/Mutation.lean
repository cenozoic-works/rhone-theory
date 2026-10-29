/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PairObservationChannel.Law

/-! # Uniform-root equal-rates observation bridge -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def transition (r : ℝ) (a b : Fin K) : ℝ :=
  (1 - r) / K + if a = b then r else 0

noncomputable def latentPair (r : ℝ) (i j : Fin K) : ℝ :=
  ∑ a : Fin K, (1 / (K : ℝ)) * transition r a i * transition r a j

theorem latent_pair_formula (hK : 0 < K) (r : ℝ) (i j : Fin K) :
    latentPair r i j = (1 - r^2) / (K : ℝ)^2 + if i = j then r^2 / K else 0 := by
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  unfold latentPair transition
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  by_cases hij : i = j
  · subst j
    simp [mul_ite, ite_mul, Finset.sum_const]
    field_simp
    ring1
  · simp [mul_ite, ite_mul, hij, Ne.symm hij, Finset.sum_const]
    field_simp
    ring1

noncomputable def reportedFromMutation (E : Channel K H) (r : ℝ) (x y : H) : ℝ :=
  ∑ i, ∑ j, latentPair r i j * E.row i x * E.row j y

theorem reported_from_mutation (E : Channel K H) (r : ℝ) (x y : H) :
    reportedFromMutation E r x y = reportedMass E (r^2) x y := by
  have hk : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt E.positive)
  unfold reportedFromMutation
  simp_rw [latent_pair_formula E.positive, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [reportedMass, columnMean, sharedMass, div_eq_mul_inv,
    mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp

end Rhone.Statistics.PairObservationChannel
