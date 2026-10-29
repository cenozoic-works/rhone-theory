/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PairIntegrableFlow
public import Rhone.Statistics.Identifiability.IntegrableMarkovMass

/-! # Proper initial pair survival forces divergent coalescence exposure for L1 sources -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.PairIntegrable

lemma survival_lower_bound (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-integratedClock c t) ≤ timeVaryingPairSurvival k c q 0 0 t := by
  have hQi := generator_locallyIntegrable k c q hc hq
  have h := integrable_finiteRowODE_mass_clock_lower_bound
    (fun u => MarkovChain.Identifiability.pairGenerator k (c u) (q u))
        (fun u => timeVaryingPairTransition k c q 0 u 0) c
    (fun u _ j => integrableTransition_entry_ac_right _ hQi 0 0 u 0 j) (by
      filter_upwards [integrableTransition_ae_hasDerivAt_right _ hQi] with u hu _ j
      exact hu 0 0 j)
    (fun u hu j => transition_nonnegative k c q hc hq hqn le_rfl hu 0 j) hc (by
      filter_upwards [hcn] with u hu hnonneg i
      exact (timeVaryingPairGenerator_row_bounds k (hu hnonneg) i).1) ht
  simpa [timeVaryingPairTransition, timeVaryingPairSurvival, integratedClock,
    integrableTransition_self _ hQi] using h

lemma coalescence_clock_diverges (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    Tendsto (integratedClock c) atTop atTop := by
  apply tendsto_atTop_of_survival_lower_bound (timeVaryingPairSurvival k c q 0 0)
    (integratedClock c) (a := 1) (by norm_num) hproper
  intro t ht
  simpa only [one_mul] using survival_lower_bound k c q hc hq hcn hqn ht

end Rhone.Statistics.Identifiability.PairIntegrable
