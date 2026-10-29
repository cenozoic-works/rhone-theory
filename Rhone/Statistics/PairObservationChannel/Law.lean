/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PairObservationChannel.Agreement
public import Mathlib.Data.Fintype.BigOperators

/-! # Normalized full finite reported-pair law for the stationary pair mixture -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.PairObservationChannel
open DependenceBudget
variable {K : ℕ} {H : Type*} [Fintype H]

theorem shared_mass_nonneg (E : Channel K H) (x y : H) : 0 ≤ sharedMass E x y := by
  exact div_nonneg (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (E.nonneg i x) (E.nonneg i y))) (Nat.cast_nonneg K)

theorem shared_mass_marginal (E : Channel K H) (x : H) :
    ∑ y, sharedMass E x y = columnMean E x := by
  simp only [sharedMass, div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, E.normalized, mul_one, columnMean, div_eq_mul_inv]

theorem reported_mass_marginal (E : Channel K H) (ℓ : ℝ) (x : H) :
    ∑ y, reportedMass E ℓ x y = columnMean E x := by
  simp only [reportedMass, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [column_mean_total, shared_mass_marginal]
  ring1

noncomputable def reportedLaw (E : Channel K H) (ℓ : ℝ) (hℓ : 0 ≤ ℓ ∧ ℓ ≤ 1) :
    Law (H × H) where
  mass := fun xy => reportedMass E ℓ xy.1 xy.2
  nonneg := by
    intro xy
    unfold reportedMass
    exact add_nonneg
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hℓ.2) (column_mean_nonneg E xy.1))
        (column_mean_nonneg E xy.2))
      (mul_nonneg hℓ.1 (shared_mass_nonneg E xy.1 xy.2))
  total := by
    rw [Fintype.sum_prod_type]
    simp only [reported_mass_marginal, column_mean_total]

theorem agreement_as_expectation [DecidableEq H] (E : Channel K H) (ℓ : ℝ) (hℓ : 0 ≤ ℓ ∧ ℓ ≤ 1) :
    rejection (reportedLaw E ℓ hℓ) (fun xy => if xy.1 = xy.2 then 1 else 0) =
      agreement E ℓ := by
  classical
  simp [rejection, reportedLaw, Fintype.sum_prod_type, agreement]

theorem erased_mass (E : Channel K H) (hE : retainedVariance E = 0)
    (ℓ : ℝ) (x y : H) : reportedMass E ℓ x y = columnMean E x * columnMean E y := by
  have hrow := (retained_variance_zero_iff E).mp hE
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt E.positive)
  unfold reportedMass sharedMass
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring1

theorem reported_mass_eq_iff (E : Channel K H) (ℓ₁ ℓ₂ : ℝ) :
    (∀ x y, reportedMass E ℓ₁ x y = reportedMass E ℓ₂ x y) ↔
      ℓ₁ = ℓ₂ ∨ retainedVariance E = 0 := by
  constructor
  · intro h
    by_cases hE : retainedVariance E = 0
    · exact Or.inr hE
    · have hv : Informative E := (retained_variance_pos_iff E).mp
        (lt_of_le_of_ne (retained_variance_nonneg E) (Ne.symm hE))
      apply Or.inl
      apply informative_agreement_injective E hv
      exact Finset.sum_congr rfl (fun x _ => h x x)
  · rintro (rfl | hE) x y
    · rfl
    · rw [erased_mass E hE, erased_mass E hE]

end Rhone.Statistics.PairObservationChannel
