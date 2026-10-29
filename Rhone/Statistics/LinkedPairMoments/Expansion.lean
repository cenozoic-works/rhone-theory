/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.Kernel

/-! # Exact subset expansion of full labelled linked-panel pattern weights -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedPairMoments
open DependenceBudget PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def panelCoefficient (E : Channel K H) {L : ℕ} (x : Fin L → H × H)
    (S : Finset (Fin L)) : ℝ :=
  (∏ i ∈ S, (sharedMass E (x i).1 (x i).2 -
    columnMean E (x i).1 * columnMean E (x i).2)) *
    ∏ i ∈ Sᶜ, columnMean E (x i).1 * columnMean E (x i).2

theorem conditional_weight_expansion (E : Channel K H) (k t : ℝ) (L : ℕ)
    (x : Fin L → H × H) :
    panelWeight E k t L x = ∑ S : Finset (Fin L),
      panelCoefficient E x S * Real.exp (-((S.card : ℝ) * k) * t) := by
  have he : ∀ i : Fin L, reportedMass E (Real.exp (-k * t)) (x i).1 (x i).2 =
      (sharedMass E (x i).1 (x i).2 - columnMean E (x i).1 * columnMean E (x i).2) *
        Real.exp (-k * t) + columnMean E (x i).1 * columnMean E (x i).2 := by
    intro i
    unfold reportedMass
    ring1
  unfold panelWeight
  simp_rw [he]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul]
  have hx : (S.card : ℝ) * (-k * t) = -((S.card : ℝ) * k) * t := by ring1
  rw [hx]
  unfold panelCoefficient
  ring1

theorem panel_weight_expansion (E : Channel K H) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t)
    (L : ℕ) (x : Fin L → H × H) :
    (panelLaw E μ hk hμ L).mass x = ∑ S : Finset (Fin L),
      panelCoefficient E x S * pairLaplace μ ((S.card : ℝ) * k) := by
  change (∫ t, panelWeight E k t L x ∂μ) = _
  simp_rw [conditional_weight_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro S _
    rw [integral_const_mul]
    rfl
  · intro S _
    exact (exp_integrable μ (mul_nonneg (Nat.cast_nonneg _) hk) hμ).const_mul _

theorem finite_law_ext {X : Type*} [Fintype X] (P Q : Law X)
    (h : ∀ x, P.mass x = Q.mass x) : P = Q := by
  cases P with
  | mk p hp ht =>
    cases Q with
    | mk q hq hs =>
      have he : p = q := funext h
      cases he
      rfl

theorem panel_eq_of_moments (E : Channel K H) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ)
    (hm : ∀ r : ℕ, r ≤ L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k)) :
    panelLaw E μ hk hμ L = panelLaw E ν hk hν L := by
  apply finite_law_ext
  intro x
  rw [panel_weight_expansion, panel_weight_expansion]
  apply Finset.sum_congr rfl
  intro S _
  rw [hm S.card (by simpa using Finset.card_le_univ S)]

end Rhone.Statistics.LinkedPairMoments
