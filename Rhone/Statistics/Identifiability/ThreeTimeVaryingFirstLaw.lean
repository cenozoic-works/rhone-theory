/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingProjection
public import Rhone.Statistics.Identifiability.ExitCDF

/-! # The first-merger law and its CDF follow from the survival derivative -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

def firstLaw (k : ℕ) (c q : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (firstDensity k c q t))

lemma firstCDF_derivative (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (t : ℝ) : HasDerivAt (fun u => 1 - survival k c q u) (firstDensity k c q t) t := by
  simpa only [neg_neg] using (survival_derivative k c q hc hq t).const_sub 1

lemma firstLaw_real_Ioc (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {T : ℝ} (hT : 0 ≤ T) : (firstLaw k c q).real (Ioc 0 T) = 1 - survival k c q T := by
  have hi : IntervalIntegrable (firstDensity k c q) volume 0 T :=
    (firstDensity_continuous k c q hc hq).intervalIntegrable 0 T
  rw [firstLaw, positive_density_real_Ioc _ hT hi]
  · have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => firstCDF_derivative k c q hc hq t) hi
    simpa only [survival_initial k c q hc hq, sub_self, sub_zero] using he
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact firstDensity_nonnegative k c q hc hq hcn hqn ht.1.le

lemma firstDensity_lintegral_one (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hproper : Tendsto (timeVaryingPairSurvival k c q 0 0) atTop (𝓝 0)) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (firstDensity k c q t)) = 1 := by
  have hlim := (survival_tendsto_zero_of_pair k c q hc hq hcn hqn hproper).const_sub 1
  have hi := integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => firstCDF_derivative k c q hc hq t)
    (fun t ht => firstDensity_nonnegative k c q hc hq hcn hqn ht.le) hlim
  have he := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => firstCDF_derivative k c q hc hq t)
    (fun t ht => firstDensity_nonnegative k c q hc hq hcn hqn ht.le) hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [he]
    simp only [survival_initial k c q hc hq, sub_self, sub_zero, ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact firstDensity_nonnegative k c q hc hq hcn hqn ht.le

end Rhone.Statistics.Identifiability.ThreeTimeVarying
