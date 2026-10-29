/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.Kernel
public import Rhone.Statistics.PairObservationChannel.Observation

/-! # First-site marginal of a shared-time two-site observation -/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LinkedPairTimes
open DependenceBudget PairObservationChannel LinkedPairMoments
variable {K : ℕ} {H : Type*} [Fintype H]

theorem reported_mass_total (E : Channel K H) (ℓ : ℝ) :
    ∑ x : H × H, reportedMass E ℓ x.1 x.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [reported_mass_marginal, column_mean_total]

theorem first_site_marginal (E : Channel K H) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {k : ℝ} (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (x : H × H) :
    (∑ y : H × H, (panelLaw E μ hk hμ 2).mass ![x, y]) =
      reportedMass E (pairLaplace μ k) x.1 x.2 := by
  change (∑ y : H × H, ∫ t, panelWeight E k t 2 ![x, y] ∂μ) = _
  rw [← integral_finsetSum _ (fun y _ => panel_weight_integrable E μ hk hμ 2 ![x, y])]
  rw [← observed_mass_formula E μ hk hμ x.1 x.2]
  unfold observedMass
  apply integral_congr_ae
  filter_upwards [] with t
  simp [panelWeight, Fin.prod_univ_two, ← Finset.mul_sum, reported_mass_total,
    conditionalMass_eq_reportedMass]

end Rhone.Statistics.LinkedPairTimes
