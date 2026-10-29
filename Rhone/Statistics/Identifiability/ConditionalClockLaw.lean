/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FirstExitLaw

/-! # Proper conditional pair-time laws for a nonautonomous coalescence clock -/

@[expose] public section

open scoped Topology
open Filter Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

noncomputable def conditionalPairDensity (rate H : ℝ → ℝ) (s t : ℝ) : ℝ :=
  rate t * Real.exp (H s-H t)

theorem conditionalPair_CDF_derivative (rate H : ℝ → ℝ) (s t : ℝ)
    (hH : HasDerivAt H (rate t) t) :
    HasDerivAt (fun x => 1-Real.exp (H s-H x)) (conditionalPairDensity rate H s t) t := by
  convert! (hH.const_sub (H s)).exp.const_sub 1 using 1
  unfold conditionalPairDensity
  ring

theorem conditionalPair_survival_tendsto_zero (H : ℝ → ℝ) (s : ℝ)
    (hH : Tendsto H atTop atTop) :
    Tendsto (fun t => Real.exp (H s-H t)) atTop (𝓝 0) := by
  have h := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hH)).const_mul
    (Real.exp (H s))
  simpa only [sub_eq_add_neg,Real.exp_add,mul_zero,Function.comp_apply] using h

theorem conditionalPair_integrable (rate H : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (htail : Tendsto H atTop atTop) :
    IntegrableOn (conditionalPairDensity rate H s) (Ioi s) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => conditionalPair_CDF_derivative rate H s t (hd t (le_trans hs ht)))
    (fun t ht => mul_nonneg (hr t (le_trans hs ht.le)) (Real.exp_pos _).le)
  exact (conditionalPair_survival_tendsto_zero H s htail).const_sub 1

theorem conditionalPair_integral_one (rate H : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (htail : Tendsto H atTop atTop) :
    (∫ t in Ioi s, conditionalPairDensity rate H s t) = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t ht => conditionalPair_CDF_derivative rate H s t (hd t (le_trans hs ht)))
    (fun t ht => mul_nonneg (hr t (le_trans hs ht.le)) (Real.exp_pos (H s-H t)).le)
    ((conditionalPair_survival_tendsto_zero H s htail).const_sub 1)
  simpa using h

theorem conditionalPair_lintegral_one (rate H : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (htail : Tendsto H atTop atTop) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (conditionalPairDensity rate H s t)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (conditionalPair_integrable rate H hs hr hd htail)]
  · rw [conditionalPair_integral_one rate H hs hr hd htail,ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (hr t (le_trans hs ht.le)) (Real.exp_pos _).le

end Rhone.Statistics.Identifiability
