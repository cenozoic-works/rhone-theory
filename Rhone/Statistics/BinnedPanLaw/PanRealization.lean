/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.CDF

/-! # Proper deterministic pan realization of every positive equal-width histogram -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Rhone.Statistics.BinnedPanLaw
open AtomicSmoothing Algebra.Identifiability MarkovChain.Identifiability Identifiability
    ThreeSampleMembership
variable {n : ℕ}

def survival (w : Fin n → ℝ) (t : ℝ) : ℝ := histogramCDF w (unitClock t)

theorem survival_lipschitz (w : Fin n → ℝ) : ∃ K, LipschitzWith K (survival w) := by
  obtain ⟨K, hK⟩ := histogramCDF_lipschitz w
  exact ⟨K * 1, hK.comp unitClock_lipschitz⟩

theorem survival_antitone (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) : Antitone (survival w) :=
  fun _ _ h => histogramCDF_monotone w (fun i => (hw i).le) (unitClock_antitone h)

def regularSurvival (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hs : ∑ i, w i = 1) : RegularPairSurvival where
  u := survival w
  d := deriv (survival w)
  continuous_u := (survival_lipschitz w).choose_spec.continuous
  locallyIntegrable_d := lipschitz_deriv_locallyIntegrable (survival_lipschitz w).choose_spec
  ac := fun _ _ => (survival_lipschitz w).choose_spec.lipschitzOnWith
    |>.absolutelyContinuousOnInterval
  derivative_ae := ((survival_lipschitz w).choose_spec.ae_differentiableAt_real).mono
    (fun _ ht _ => ht.hasDerivAt)
  initial := by rw [survival, unitClock_zero, histogramCDF_one w hs]
  positive := fun t _ => histogramCDF_positive hn w hw (unitClock_positive t)
  decreasing_ae := ae_of_all _ fun _ _ => (survival_antitone w hw).deriv_nonpos
  proper := by
    have h := (histogramCDF_lipschitz w).choose_spec.continuous.continuousAt.tendsto.comp
      unitClock_tendsto
    rw [histogramCDF_zero] at h
    exact h

theorem exists_pan_histogram (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hs : ∑ i, w i = 1) :
    ∃ r : ℝ → ℝ, LocallyIntegrable r volume ∧ (∀ t, 0 ≤ r t) ∧
      Tendsto (integratedClock r) atTop atTop ∧
      (panPairLaw r).map (fun t : ℝ => Real.exp (-t)) = histogram w := by
  let P := regularSurvival hn w hw hs
  let r := P.firstProfile.rate
  have hr := P.firstProfile.rate_locallyIntegrable
  have hnn := P.firstProfile.rate_nonnegative
  have ht := P.firstProfile.clock_diverges
  have he (t : ℝ) (ht0 : 0 ≤ t) :
      Real.exp (-integratedClock r t) = histogramCDF w (Real.exp (-t)) := by
    rw [← P.survival_eq_clock ht0]
    change survival w t = _
    rw [survival, unitClock_eq ht0]
  refine ⟨r, hr, hnn, ht, ?_⟩
  let : IsProbabilityMeasure (panPairLaw r) := PanThreeSample.pairLaw_probability r hr hnn ht
  let : IsProbabilityMeasure ((panPairLaw r).map (fun t : ℝ => Real.exp (-t))) :=
    inferInstance
  let : IsProbabilityMeasure (histogram w) := histogram_probability w (fun i => (hw i).le) hs
  apply Measure.ext_of_Iic
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((panPairLaw r).map (fun t : ℝ => Real.exp (-t))).real (Iic x) =
    (histogram w).real (Iic x)
  rw [histogram_real_Iic hn w (fun i => (hw i).le)]
  by_cases hx : x ≤ 0
  · rw [pan_pair_transform_below r hx]
    symm
    apply le_antisymm
    · exact (histogramCDF_monotone w (fun i => (hw i).le) hx).trans_eq
        (histogramCDF_zero w)
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (clip_nonnegative _)
  · have hx0 : 0 < x := lt_of_not_ge hx
    by_cases hx1 : x ≤ 1
    · rw [pan_pair_transform_inner r hr hnn ht hx0 hx1,
        he _ (neg_nonneg.mpr (Real.log_nonpos hx0.le hx1)), neg_neg, Real.exp_log hx0]
    · rw [pan_pair_transform_above r hr hnn ht (le_of_not_ge hx1)]
      have hge := histogramCDF_monotone w (fun i => (hw i).le) (le_of_not_ge hx1)
      rw [histogramCDF_one w hs] at hge
      apply le_antisymm hge
      calc
        _ ≤ ∑ i, w i * 1 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (clip_le_one _) (hw i).le
        _ = 1 := by simpa using hs

end Rhone.Statistics.BinnedPanLaw
