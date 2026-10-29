/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PairObservationChannel.LaplaceKernel
public import Rhone.Statistics.PairObservationChannel.Mutation
public import Rhone.Statistics.Identifiability.EqualRatesMutationSemigroup

/-! # Observer bridge for the equal-rates pair-time channel -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable abbrev ER := Identifiability.EqualRatesMutation.transition

theorem transition_eq_semigroup (k t : ℝ) (a b : Fin K) :
    transition (Real.exp (-(k / 2) * t)) a b = ER K k t a b := by
  change (1 - Real.exp (-(k / 2) * t)) / K +
      (if a = b then Real.exp (-(k / 2) * t) else 0) =
    Real.exp (-(k / 2) * t) * (if a = b then 1 else 0) +
      (1 - Real.exp (-(k / 2) * t)) * (1 / (K : ℝ))
  split_ifs <;> ring

noncomputable def conditionalMass (E : Channel K H) (k t : ℝ) (x y : H) : ℝ :=
  ∑ i, ∑ j, Identifiability.EqualRatesMutation.ancestralPair K k t i j *
    E.row i x * E.row j y

theorem conditionalMass_eq_reportedMass (E : Channel K H) (k t : ℝ) (x y : H) :
    conditionalMass E k t x y = reportedMass E (Real.exp (-k * t)) x y := by
  have hp : ∀ i j : Fin K,
      Identifiability.EqualRatesMutation.ancestralPair K k t i j =
        latentPair (Real.exp (-(k / 2) * t)) i j := by
    intro i j
    unfold Identifiability.EqualRatesMutation.ancestralPair latentPair
    simp_rw [transition_eq_semigroup]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold conditionalMass
  simp_rw [hp]
  change reportedFromMutation E (Real.exp (-(k / 2) * t)) x y = _
  rw [reported_from_mutation]
  have he : (Real.exp (-(k / 2) * t)) ^ 2 = Real.exp (-k * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]

noncomputable def observedMass (E : Channel K H) (μ : Measure ℝ) (k : ℝ) (x y : H) : ℝ :=
  ∫ t, conditionalMass E k t x y ∂μ

theorem observed_mass_formula (E : Channel K H) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (x y : H) :
    observedMass E μ k x y = reportedMass E (pairLaplace μ k) x y := by
  have hi := exp_integrable μ hk hμ
  have he (t : ℝ) : conditionalMass E k t x y =
      columnMean E x * columnMean E y + Real.exp (-k * t) *
        (sharedMass E x y - columnMean E x * columnMean E y) := by
    rw [conditionalMass_eq_reportedMass]
    unfold reportedMass
    ring
  unfold observedMass
  simp_rw [he]
  rw [integral_add (integrable_const _) (hi.mul_const _),
    integral_mul_const (sharedMass E x y - columnMean E x * columnMean E y)]
  simp only [integral_const, probReal_univ, one_smul]
  unfold pairLaplace reportedMass
  ring

end Rhone.Statistics.PairObservationChannel
