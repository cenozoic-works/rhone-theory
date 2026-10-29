/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegratedClock
public import Rhone.Statistics.Identifiability.ConditionalClockLaw

/-! # Literal first-recombination measure on a finite coalescence-free interval -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.SilentWindow

def noSplit (r : ℝ → ℝ) (T : ℝ) : ℝ := Real.exp (-integratedClock r T)

def splitDensity (r : ℝ → ℝ) (u : ℝ) : ℝ := r u * noSplit r u

def splitLaw (r : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 T)).withDensity (fun u => ENNReal.ofReal (splitDensity r u))

lemma splitDensity_continuous (r : ℝ → ℝ) (hr : Continuous r) : Continuous (splitDensity r) :=
  hr.mul (Real.continuous_exp.comp (integratedClock_continuous r hr.locallyIntegrable).neg)

lemma splitDensity_integral (r : ℝ → ℝ) (hr : Continuous r) (T : ℝ) :
    (∫ u in (0 : ℝ)..T, splitDensity r u) = 1 - noSplit r T := by
  have hclock (u : ℝ) : HasDerivAt (integratedClock r) (r u) u :=
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 u)
      hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hd (u : ℝ) : HasDerivAt (fun v => 1 - noSplit r v) (splitDensity r u) u := by
    simpa [conditionalPairDensity, noSplit, splitDensity, integratedClock] using
      conditionalPair_CDF_derivative r (integratedClock r) 0 u (hclock u)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((splitDensity_continuous r hr).intervalIntegrable 0 T)
  simpa [noSplit, integratedClock] using h

lemma noSplit_positive (r : ℝ → ℝ) (T : ℝ) : 0 < noSplit r T := Real.exp_pos _

lemma noSplit_le_one (r : ℝ → ℝ) (hrn : ∀ u, 0 ≤ u → 0 ≤ r u)
    {T : ℝ} (hT : 0 ≤ T) : noSplit r T ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  exact intervalIntegral.integral_nonneg hT (fun u hu => hrn u hu.1)

lemma noSplit_lt_one_of_exposure (r : ℝ → ℝ) {T : ℝ}
    (hexp : 0 < integratedClock r T) : noSplit r T < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_of_pos hexp)

theorem splitLaw_mass (r : ℝ → ℝ) (hr : Continuous r)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {T : ℝ} (hT : 0 ≤ T) :
    splitLaw r T Set.univ = ENNReal.ofReal (1 - noSplit r T) := by
  have hi : IntegrableOn (splitDensity r) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      ((splitDensity_continuous r hr).intervalIntegrable 0 T)
  have hn : ∀ᵐ u ∂volume.restrict (Ioc 0 T), 0 ≤ splitDensity r u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact mul_nonneg (hrn u hu.1.le) (noSplit_positive r u).le
  rw [splitLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le hT, splitDensity_integral r hr]

theorem splitLaw_finite (r : ℝ → ℝ) (hr : Continuous r)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {T : ℝ} (hT : 0 ≤ T) :
    IsFiniteMeasure (splitLaw r T) :=
  ⟨by rw [splitLaw_mass r hr hrn hT]; exact ENNReal.ofReal_lt_top⟩

theorem splitLaw_real_mass (r : ℝ → ℝ) (hr : Continuous r)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {T : ℝ} (hT : 0 ≤ T) :
    (splitLaw r T).real Set.univ = 1 - noSplit r T := by
  rw [measureReal_def, splitLaw_mass r hr hrn hT,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (noSplit_le_one r hrn hT))]

end Rhone.Statistics.Identifiability.SilentWindow
