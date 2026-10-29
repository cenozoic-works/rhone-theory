/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableProjection

/-! # First-merger CDF and normalization for locally L1 source rates -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.ThreeIntegrable
open ThreeTimeVarying

lemma firstLaw_real_Ioc (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    {T : ℝ} (hT : 0 ≤ T) : (firstLaw k c q).real (Ioc 0 T) = 1 - survival k c q T := by
  have hi := locallyIntegrable_interval _ (firstDensity_locallyIntegrable k c q hc hq) 0 T
  rw [firstLaw, positive_density_real_Ioc _ hT hi]
  · have hac : AbsolutelyContinuousOnInterval (fun u => 1 - survival k c q u) 0 T :=
      (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.sub
        (survival_ac k c q hc hq 0 T)
    have he := ac_integral_eq_sub_ae hac (by
      filter_upwards [survival_derivative_ae k c q hc hq] with u hu _
      simpa only [neg_neg] using hu.const_sub 1)
    simpa only [survival_initial k c q hc hq, sub_self, sub_zero] using he
  · filter_upwards [(firstDensity_nonnegative_ae k c q hc hq hcn hqn).filter_mono
      (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioc] with u hu hmem
    exact hu hmem.1.le

lemma firstDensity_lintegral_one (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (firstDensity k c q t)) = 1 := by
  have he := ac_flux_lintegral_Ioi (fun b _ => survival_ac k c q hc hq 0 b) (by
    filter_upwards [survival_derivative_ae k c q hc hq] with u hu _
    exact hu) (firstDensity_nonnegative_ae k c q hc hq hcn hqn)
    (firstDensity_locallyIntegrable k c q hc hq).aestronglyMeasurable.aemeasurable.restrict
    (survival_tendsto_zero_of_pair k c q hc hq hcn hqn hproper)
  simpa only [survival_initial k c q hc hq, sub_zero, ENNReal.ofReal_one] using he

end Rhone.Statistics.Identifiability.ThreeIntegrable
