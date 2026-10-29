/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PairObservationChannel.Channel

/-! # The agreement formula for the stationary equal-rates pair mixture -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def sharedMass (E : Channel K H) (x y : H) : ℝ :=
  (∑ i, E.row i x * E.row i y) / K

noncomputable def reportedMass (E : Channel K H) (ℓ : ℝ) (x y : H) : ℝ :=
  (1-ℓ)*columnMean E x*columnMean E y + ℓ*sharedMass E x y

noncomputable def agreement (E : Channel K H) (ℓ : ℝ) : ℝ :=
  ∑ y, reportedMass E ℓ y y

theorem column_variance_identity (E : Channel K H) (y : H) :
    ∑ i, (E.row i y-columnMean E y)^2 =
      (∑ i, (E.row i y)^2) - K*(columnMean E y)^2 := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt E.positive)
  have hm : (∑ i, E.row i y) = K*columnMean E y := by
    unfold columnMean
    field_simp
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  rw [hm]
  ring1

theorem retained_variance_formula (E : Channel K H) :
    retainedVariance E = (∑ y, sharedMass E y y) - baseline E := by
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt E.positive)
  unfold retainedVariance
  rw [Finset.sum_comm]
  simp_rw [column_variance_identity]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sharedMass, baseline,
    div_eq_mul_inv, ← Finset.sum_mul, ← sq]
  field_simp

theorem agreement_formula (E : Channel K H) (ℓ : ℝ) :
    agreement E ℓ = baseline E + retainedVariance E * ℓ := by
  rw [retained_variance_formula]
  unfold agreement reportedMass baseline
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ← sq]
  ring1

theorem agreement_gap (E : Channel K H) (ℓ₁ ℓ₂ : ℝ) :
    agreement E ℓ₁-agreement E ℓ₂ = retainedVariance E*(ℓ₁-ℓ₂) := by
  rw [agreement_formula, agreement_formula]
  ring1

theorem informative_agreement_injective (E : Channel K H) (hE : Informative E) :
    Function.Injective (agreement E) := by
  intro x y h
  have hv := (retained_variance_pos_iff E).mpr hE
  have hz : retainedVariance E*(x-y) = 0 := by rw [← agreement_gap, h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hv.ne')

end Rhone.Statistics.PairObservationChannel
