/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.Kernel
public import Rhone.Statistics.DependentPairedTest.MomentAlgebra

/-! # Centred-agreement product extraction for every subset of a linked panel -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedPairMoments
open DependenceBudget DependentPairedTest PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def centeredAgreement (E : Channel K H) (x : H × H) : ℝ :=
  (if x.1 = x.2 then 1 else 0) - baseline E

noncomputable def panelStatistic (E : Channel K H) {L : ℕ} (S : Finset (Fin L))
    (x : Fin L → H × H) : ℝ := ∏ i ∈ S, centeredAgreement E (x i)

theorem centered_agreement_mean (E : Channel K H) (ℓ : ℝ) (hℓ : 0 ≤ ℓ ∧ ℓ ≤ 1) :
    rejection (reportedLaw E ℓ hℓ) (centeredAgreement E) = retainedVariance E * ℓ := by
  have he : rejection (reportedLaw E ℓ hℓ) (centeredAgreement E) =
      rejection (reportedLaw E ℓ hℓ) (fun x => if x.1 = x.2 then 1 else 0) - baseline E := by
    simp [rejection, centeredAgreement, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, (reportedLaw E ℓ hℓ).total]
  rw [he, agreement_as_expectation, agreement_formula]
  ring1

theorem conditional_statistic_mean (E : Channel K H) {k t : ℝ}
    (hk : 0 ≤ k) (ht : 0 ≤ t) {L : ℕ} (S : Finset (Fin L)) :
    (∑ x, panelWeight E k t L x * panelStatistic E S x) =
      (retainedVariance E * Real.exp (-k * t)) ^ S.card := by
  have h := conditional_product_expectation E hk ht L
    (fun i x => if i ∈ S then centeredAgreement E x else 1)
  have he : ∀ i : Fin L,
      rejection (reportedLaw E _ (exp_parameter_bounds hk ht))
        (fun x => if i ∈ S then centeredAgreement E x else 1) =
      if i ∈ S then retainedVariance E * Real.exp (-k * t) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [ite_eq_left hi]
      exact centered_agreement_mean E _ _
    · simp only [ite_eq_right hi]
      exact expectation_const _ 1
  simp_rw [he] at h
  simpa only [Finset.prod_ite_mem_eq, Finset.prod_const, panelStatistic] using h

theorem panel_statistic_mean (E : Channel K H) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    {L : ℕ} (S : Finset (Fin L)) :
    rejection (panelLaw E μ hk hμ L) (panelStatistic E S) =
      retainedVariance E ^ S.card * pairLaplace μ ((S.card : ℝ) * k) := by
  rw [panelLaw, finite_mixture_expectation]
  have he : ∀ᵐ t ∂μ, (∑ x, panelWeight E k t L x * panelStatistic E S x) =
      retainedVariance E ^ S.card * Real.exp (-((S.card : ℝ) * k) * t) := by
    filter_upwards [hμ] with t ht
    rw [conditional_statistic_mean E hk ht, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring1
  rw [integral_congr_ae he, integral_const_mul]
  rfl

end Rhone.Statistics.LinkedPairMoments
