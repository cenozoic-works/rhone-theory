/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingKernel
public import Rhone.Statistics.Identifiability.ThreeIntegrableFirstLaw

/-! # The first-merger CDF for an arbitrary initial occupancy row -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling

lemma survival_initial (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρsum : ∑ i, ρ i = 1) (hc : LocallyIntegrable c volume)
    (hq : LocallyIntegrable q volume) : survival ρ k c q 0 = 1 := by
  unfold survival
  rw [preRow_initial ρ k c q hc hq]
  exact hρsum

lemma firstDensity_nonnegative_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) :
    ∀ᵐ t, 0 ≤ t → 0 ≤ firstDensity ρ k c q t := by
  filter_upwards [hcn] with t ht ht0
  have h0 := preRow_nonnegative ρ k c q hρ hc hq hqn ht0 0
  have h1 := preRow_nonnegative ρ k c q hρ hc hq hqn ht0 1
  exact mul_nonneg (ht ht0) (by positivity)

lemma firstLaw_real_Ioc (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    {T : ℝ} (hT : 0 ≤ T) :
    (firstLaw ρ k c q).real (Ioc 0 T) = 1 - survival ρ k c q T := by
  have hi := locallyIntegrable_interval _ (firstDensity_locallyIntegrable ρ k c q hc hq) 0 T
  rw [firstLaw, positive_density_real_Ioc _ hT hi]
  · have hac : AbsolutelyContinuousOnInterval (fun u => 1 - survival ρ k c q u) 0 T :=
      (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.sub
        (survival_ac ρ k c q hc hq 0 T)
    have he := ac_integral_eq_sub_ae hac (by
      filter_upwards [survival_derivative_ae ρ k c q hc hq] with u hu _
      simpa only [firstDensity, neg_mul, neg_neg] using hu.const_sub 1)
    simpa only [survival_initial ρ k c q hρsum hc hq, sub_self, sub_zero, firstDensity] using he
  · filter_upwards [(firstDensity_nonnegative_ae ρ k c q hρ hc hq hcn hqn).filter_mono
      (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioc] with u hu hmem
    exact hu hmem.1.le

end Rhone.Statistics.Identifiability.ThreeSampling
