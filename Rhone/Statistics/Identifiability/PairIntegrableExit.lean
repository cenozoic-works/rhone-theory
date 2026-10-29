/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PairIntegrableFlow
public import Rhone.Statistics.Identifiability.IntegrableClockCalculus

/-! # Proper conditional pair-exit densities for the locally L1 evolution -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix ENNReal
namespace Rhone.Statistics.Identifiability.PairIntegrable

lemma survival_self (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (s : ℝ) (i : Fin 2) :
    timeVaryingPairSurvival k c q s i s = 1 := by
  fin_cases i <;> simp [timeVaryingPairSurvival, timeVaryingPairTransition,
    integrableTransition_self _ (generator_locallyIntegrable k c q hc hq)]

lemma exitDensity_locallyIntegrable (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) (s : ℝ) (i : Fin 2) :
    LocallyIntegrable (timeVaryingPairExitDensity k c q s i) volume := by
  have hU := transition_continuous k c q hc hq
  have hp : Continuous (fun t => timeVaryingPairTransition k c q s t i 0) := by fun_prop
  exact hc.continuous_mul hp

lemma exitDensity_nonnegative_ae (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin 2) :
    ∀ᵐ t, s ≤ t → 0 ≤ timeVaryingPairExitDensity k c q s i t := by
  filter_upwards [hcn] with t ht hst
  exact mul_nonneg (transition_nonnegative k c q hc hq hqn hs hst i 0) (ht (hs.trans hst))

lemma exitDensity_lintegral_one (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin 2)
    (hproper : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t)) = 1 := by
  have hm := (exitDensity_locallyIntegrable k c q hc hq s i).aestronglyMeasurable.aemeasurable
  have he := ac_flux_lintegral_Ioi (fun b _ => survival_ac k c q hc hq s s b i) (by
    filter_upwards [survival_derivative_ae k c q hc hq] with t ht _
    exact ht s i) (exitDensity_nonnegative_ae k c q hc hq hcn hqn hs i)
    hm.restrict hproper
  simpa only [survival_self k c q hc hq s i, sub_zero, ENNReal.ofReal_one] using he

end Rhone.Statistics.Identifiability.PairIntegrable
