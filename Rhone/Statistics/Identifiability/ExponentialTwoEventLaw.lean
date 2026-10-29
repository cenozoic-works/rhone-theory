/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ACFluxMassBound
public import Rhone.Statistics.Identifiability.AEDensityMarginals

/-! # Two independent positive exponential durations, written in ordered event coordinates -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.ExponentialTwoEvent

def shiftedDensity (a s t : ℝ) : ℝ := a * Real.exp (-a * (t - s))

lemma shifted_lintegral {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (shiftedDensity a s t)) = 1 := by
  let F := fun t => Real.exp (-a * (t - s))
  have hac (b : ℝ) (_ : s ≤ b) : AbsolutelyContinuousOnInterval F s b := by
    apply ac_exp
    exact ((LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval).sub
      (LipschitzWith.const s).lipschitzOnWith.absolutelyContinuousOnInterval).const_mul (-a)
  have hd : ∀ᵐ t, s ≤ t → HasDerivAt F (-shiftedDensity a s t) t := by
    filter_upwards [] with t _
    apply ((((hasDerivAt_id t).sub_const s).const_mul (-a)).exp).congr_deriv
    dsimp [shiftedDensity]
    ring
  have hn : ∀ᵐ t, s ≤ t → 0 ≤ shiftedDensity a s t :=
    ae_of_all _ fun t _ => mul_nonneg ha.le (Real.exp_pos _).le
  have hm : AEMeasurable (shiftedDensity a s) (volume.restrict (Ioi s)) := by
    have hcont : Continuous (shiftedDensity a s) := by unfold shiftedDensity; fun_prop
    exact hcont.measurable.aemeasurable.restrict
  have hlin : Tendsto (fun t : ℝ => t - s) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-s) tendsto_id
  have htail : Tendsto F atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [Function.comp_def, neg_mul] using
      tendsto_neg_atTop_atBot.comp (hlin.const_mul_atTop ha)
  have he := ac_flux_lintegral_Ioi hac hd hn hm htail
  simpa only [F, sub_self, mul_zero, Real.exp_zero, sub_zero, ENNReal.ofReal_one] using he

def density (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  shiftedDensity a 0 p.1 * shiftedDensity b p.1 p.2

def law (a b : ℝ) : Measure (ℝ × ℝ) := triangularDensityLaw (density a b)

lemma density_continuous (a b : ℝ) : Continuous (density a b) := by
  unfold density shiftedDensity
  fun_prop

lemma law_probability {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : IsProbabilityMeasure (law a b) := by
  constructor
  rw [law, triangularDensityLaw_mass_of_tail_ae (density a b) (shiftedDensity a 0)
    (density_continuous a b).measurable.aemeasurable.restrict]
  · exact shifted_lintegral ha 0
  · filter_upwards [] with s
    have hnn : 0 ≤ shiftedDensity a 0 s := mul_nonneg ha.le (Real.exp_pos _).le
    simp only [density]
    simp_rw [ENNReal.ofReal_mul hnn]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, shifted_lintegral hb s, mul_one]

end Rhone.Statistics.Identifiability.ExponentialTwoEvent
