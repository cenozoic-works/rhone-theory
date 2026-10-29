/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.Features
public import Rhone.Statistics.DependentPairedTest.Features

/-! # All-sites-reported-agreement feature and its exact moment expansion -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedAgreementPower
open DependenceBudget DependentPairedTest
open PairObservationChannel LinkedPairMoments
variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def allAgreement {L : ℕ} (x : Fin L → H × H) : ℝ :=
  ∏ i, if (x i).1 = (x i).2 then 1 else 0

omit [Fintype H] in
theorem all_agreement_binary (L : ℕ) : Binary (allAgreement (H := H) (L := L)) := by
  intro x
  by_cases h : ∀ i, (x i).1 = (x i).2
  · exact Or.inr (by simp [allAgreement, h])
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inl (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi))

theorem all_agreement_centered_expansion (E : Channel K H) {L : ℕ}
    (x : Fin L → H × H) :
    allAgreement x = ∑ S : Finset (Fin L), panelStatistic E S x * baseline E ^ (L - S.card) := by
  have he : ∀ i : Fin L, (if (x i).1 = (x i).2 then (1 : ℝ) else 0) =
      centeredAgreement E (x i) + baseline E := by
    intro i
    unfold centeredAgreement
    ring1
  unfold allAgreement
  simp_rw [he]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  simp [panelStatistic, Finset.card_compl]

theorem all_agreement_mean_expansion (E : Channel K H) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (L : ℕ) :
    rejection (panelLaw E μ hk hμ L) allAgreement = ∑ S : Finset (Fin L),
      retainedVariance E ^ S.card * pairLaplace μ ((S.card : ℝ) * k) *
        baseline E ^ (L - S.card) := by
  change rejection _ (fun x => allAgreement x) = _
  simp_rw [all_agreement_centered_expansion E]
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro S _
  have he : rejection (panelLaw E μ hk hμ L)
      (fun x => panelStatistic E S x * baseline E ^ (L - S.card)) =
      rejection (panelLaw E μ hk hμ L) (panelStatistic E S) * baseline E ^ (L - S.card) := by
    simp only [rejection, mul_assoc, Finset.sum_mul]
  rw [he, panel_statistic_mean]

end Rhone.Statistics.LinkedAgreementPower
