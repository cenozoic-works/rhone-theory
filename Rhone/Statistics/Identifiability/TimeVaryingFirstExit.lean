/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeVaryingPairExitKernel
public import Rhone.Statistics.Identifiability.EventMarks

/-! # Time-dependent pre-first-event row and normalized first-event flux -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Rhone.Statistics.Identifiability

noncomputable def timeVaryingARGGenerator (k : ℕ) (c q r : ℝ → ℝ)
    (t : ℝ) : Matrix MarkovChain.Identifiability.State MarkovChain.Identifiability.State ℝ :=
        MarkovChain.Identifiability.generator k (c t) (q t) (r t)

theorem timeVaryingARGGenerator_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    ∀ i j, Continuous (fun t => timeVaryingARGGenerator k c q r t i j) := by
  intro i j
  dsimp [timeVaryingARGGenerator, MarkovChain.Identifiability.generator]
  fun_prop

noncomputable def timeVaryingPreRow (k : ℕ) (c q r : ℝ → ℝ)
    (t : ℝ) : MarkovChain.Identifiability.State → ℝ :=
  inhomogeneousTransition (timeVaryingARGGenerator k c q r) 0 t 0

noncomputable def timeVaryingPreSurvival (k : ℕ) (c q r : ℝ → ℝ)
    (t : ℝ) : ℝ := ∑ i, timeVaryingPreRow k c q r t i

noncomputable def timeVaryingMarkFlux (k : ℕ) (c q r : ℝ → ℝ)
    (m : Fin 5) (t : ℝ) : ℝ :=
  ∑ i, timeVaryingPreRow k c q r t i * markRates (c t) i m

noncomputable def timeVaryingFirstExitDensity (k : ℕ) (c q r : ℝ → ℝ)
    (t : ℝ) : ℝ := ∑ m, timeVaryingMarkFlux k c q r m t

theorem timeVaryingPreRow_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    Continuous (timeVaryingPreRow k c q r) := by
  exact (continuous_apply 0).comp
    ((inhomogeneousTransition_continuous _
      (timeVaryingARGGenerator_continuous k c q r hc hq hr)).comp
      (continuous_const.prodMk continuous_id))

theorem timeVaryingMarkFlux_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (m : Fin 5) :
    Continuous (timeVaryingMarkFlux k c q r m) := by
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp (timeVaryingPreRow_continuous k c q r hc hq hr)).mul
    (hc.mul continuous_const)

theorem timeVaryingPreRow_nonneg (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) {t : ℝ} (ht : 0 ≤ t) (i : MarkovChain.Identifiability.State) :
    0 ≤ timeVaryingPreRow k c q r t i :=
  inhomogeneousTransition_nonneg _ (timeVaryingARGGenerator_continuous k c q r hc hq hr)
    (fun u hu => generator_metzler k (hcn u hu) (hqn u hu) (hrn u hu)) le_rfl ht 0 i

theorem timeVaryingMarkFlux_nonneg (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) {t : ℝ} (ht : 0 ≤ t) (m : Fin 5) :
    0 ≤ timeVaryingMarkFlux k c q r m t := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (timeVaryingPreRow_nonneg k c q r hc hq hr hcn hqn hrn ht i)
    (markRates_nonneg (hcn t ht) i m)

theorem timeVaryingARGGenerator_row_balance (k : ℕ) (c q r : ℝ → ℝ)
    (t : ℝ) (i : MarkovChain.Identifiability.State) :
    (∑ j, timeVaryingARGGenerator k c q r t i j) =
      -(∑ m, markRates (c t) i m) := by
  rw [timeVaryingARGGenerator, generator_row_sum, markRates_sum]
  ring

@[simp] theorem timeVaryingPreSurvival_zero (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    timeVaryingPreSurvival k c q r 0 = 1 := by
  simp [timeVaryingPreSurvival, timeVaryingPreRow, inhomogeneousTransition_self _
    (timeVaryingARGGenerator_continuous k c q r hc hq hr), Matrix.one_apply]

theorem timeVaryingPreSurvival_hasDerivAt (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    HasDerivAt (timeVaryingPreSurvival k c q r)
      (-timeVaryingFirstExitDensity k c q r t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    inhomogeneousTransition_hasDerivAt_right _
      (timeVaryingARGGenerator_continuous k c q r hc hq hr) 0 t 0 j)
  convert! h using 1
  change -(∑ m, ∑ i, timeVaryingPreRow k c q r t i * markRates (c t) i m) =
    ∑ j, ∑ i, timeVaryingPreRow k c q r t i * timeVaryingARGGenerator k c q r t i j
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j i =>
    timeVaryingPreRow k c q r t i * timeVaryingARGGenerator k c q r t i j)]
  simp only [← Finset.mul_sum, timeVaryingARGGenerator_row_balance, mul_neg,
    Finset.sum_neg_distrib]

theorem timeVaryingFirstExitDensity_nonneg (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ timeVaryingFirstExitDensity k c q r t := by
  exact Finset.sum_nonneg fun m _ =>
    timeVaryingMarkFlux_nonneg k c q r hc hq hr hcn hqn hrn ht m

theorem timeVaryingFirstExitCDF_hasDerivAt (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    HasDerivAt (fun u => 1 - timeVaryingPreSurvival k c q r u)
      (timeVaryingFirstExitDensity k c q r t) t := by
  simpa only [neg_neg] using
    (timeVaryingPreSurvival_hasDerivAt k c q r hc hq hr t).const_sub 1

theorem timeVaryingFirstExitDensity_integrable (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (htail : Tendsto (timeVaryingPreSurvival k c q r) atTop (𝓝 0)) :
    IntegrableOn (timeVaryingFirstExitDensity k c q r) (Ioi 0) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => timeVaryingFirstExitCDF_hasDerivAt k c q r hc hq hr t)
    (fun t ht => timeVaryingFirstExitDensity_nonneg k c q r hc hq hr hcn hqn hrn ht.le)
  exact htail.const_sub 1

theorem timeVaryingFirstExitDensity_integral_one (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (htail : Tendsto (timeVaryingPreSurvival k c q r) atTop (𝓝 0)) :
    (∫ t in Ioi 0, timeVaryingFirstExitDensity k c q r t) = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => timeVaryingFirstExitCDF_hasDerivAt k c q r hc hq hr t)
    (fun t ht => timeVaryingFirstExitDensity_nonneg k c q r hc hq hr hcn hqn hrn ht.le)
    (htail.const_sub 1)
  simpa only [sub_zero, timeVaryingPreSurvival_zero k c q r hc hq hr,
    sub_self] using h

theorem timeVaryingFirstExitDensity_lintegral_one (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (htail : Tendsto (timeVaryingPreSurvival k c q r) atTop (𝓝 0)) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (timeVaryingFirstExitDensity k c q r t)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (timeVaryingFirstExitDensity_integrable k c q r hc hq hr hcn hqn hrn htail)]
  · rw [timeVaryingFirstExitDensity_integral_one k c q r hc hq hr hcn hqn hrn htail,
      ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact timeVaryingFirstExitDensity_nonneg k c q r hc hq hr hcn hqn hrn ht.le

noncomputable def timeVaryingFirstExitLaw (k : ℕ) (c q r : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (timeVaryingFirstExitDensity k c q r t))

theorem timeVaryingFirstExitLaw_probability (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hrn : ∀ t, 0 ≤ t → 0 ≤ r t)
    (htail : Tendsto (timeVaryingPreSurvival k c q r) atTop (𝓝 0)) :
    IsProbabilityMeasure (timeVaryingFirstExitLaw k c q r) := by
  constructor
  rw [timeVaryingFirstExitLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact timeVaryingFirstExitDensity_lintegral_one k c q r hc hq hr hcn hqn hrn htail

end Rhone.Statistics.Identifiability
