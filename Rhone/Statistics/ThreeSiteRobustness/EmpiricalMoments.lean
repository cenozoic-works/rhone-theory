/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.UniformMargin
public import Rhone.Statistics.Identifiability.FinitePanelConcentration

/-! # Empirical five-feature score on iid whole linked blocks -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteRobustness
open ThreeSiteSeparator ThreeTipSites DependenceBudget
open Identifiability.FinitePanelSampling

variable {K N : ℕ}

def empiricalScore (x : Fin N → Panel K 3) : ℝ :=
  scoreVector (fun i => sampleMean (panelFeatures i) x)

theorem empirical_feature_bound (hK : 3 ≤ K) (hN : 0 < N)
    (x : Fin N → Panel K 3) (i : Fin 5) : |sampleMean (panelFeatures i) x| ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sampleMean, abs_div, abs_of_pos hNr, div_le_iff₀ hNr]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    ∑ n : Fin N, |panelFeatures i (x n)| ≤ ∑ _n : Fin N, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => panelFeatures_bounded hK i (x n)
    _ = 1 * (N : ℝ) := by simp

theorem panelFeatures_integral (ρ : Measure (Panel K 3)) [IsProbabilityMeasure ρ]
    (i : Fin 5) : (∫ x, panelFeatures i x ∂ρ) =
      rejection (finiteLaw ρ) (panelFeatures i) := by
  rw [integral_fintype (by fun_prop)]
  rfl

theorem scoreVector_integral_panelFeatures (ρ : Measure (Panel K 3)) [IsProbabilityMeasure ρ] :
    scoreVector (fun i => ∫ x, panelFeatures i x ∂ρ) = patternScore ρ := by
  simp_rw [panelFeatures_integral]
  exact scoreVector_rejection_panelFeatures ρ

theorem integral_panelFeatures_bound (hK : 3 ≤ K) (ρ : Measure (Panel K 3))
    [IsProbabilityMeasure ρ] (i : Fin 5) : |∫ x, panelFeatures i x ∂ρ| ≤ 1 := by
  rw [panelFeatures_integral]
  exact bounded_mean (finiteLaw ρ) _ (panelFeatures_bounded hK i)

end Rhone.Statistics.ThreeSiteRobustness
