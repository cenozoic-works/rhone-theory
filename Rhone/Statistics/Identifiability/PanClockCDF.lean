/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanFiveSpectrum
public import Rhone.Statistics.Identifiability.PairNonidentifiability
public import Rhone.Statistics.Identifiability.ExitCDF

/-! # Observable waiting-time CDFs for arbitrary locally integrable panmictic rates -/

@[expose] public section

open scoped ENNReal
open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem panPairLaw_real_Ioc (rate : ℝ → ℝ) (hRate : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) {T : ℝ} (hT : 0 ≤ T) :
    (panPairLaw rate).real (Ioc 0 T) = 1 - Real.exp (-integratedClock rate T) := by
  let S : ℝ → ℝ := fun t => Real.exp (-integratedClock rate t)
  have hac : AbsolutelyContinuousOnInterval S 0 T :=
    ac_exp (integratedClock_ac_zero rate hRate T).neg
  have hderiv : ∀ᵐ x, x ∈ Set.uIoc 0 T →
      deriv S x = -(rate x * Real.exp (-integratedClock rate x)) := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hRate] with x hx
    intro _
    have h : HasDerivAt S (-(rate x * Real.exp (-integratedClock rate x))) x := by
      convert! (hx 0).neg.exp using 1
      dsimp [integratedClock]
      ring
    exact h.deriv
  have hFTC := hac.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_neg] at hFTC
  have hS0 : S 0 = 1 := by simp [S, integratedClock]
  rw [hS0] at hFTC
  have hInt : IntervalIntegrable
      (fun x => rate x * Real.exp (-integratedClock rate x)) volume 0 T :=
    (locallyIntegrable_interval rate hRate 0 T).mul_continuousOn
      (Real.continuous_exp.comp (integratedClock_continuous rate hRate).neg).continuousOn
  unfold panPairLaw
  change ((volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (rate t * Real.exp (-integratedClock rate t)))).real (Ioc 0 T) = _
  rw [positive_density_real_Ioc _ hT hInt]
  · change (∫ x in 0..T, rate x * Real.exp (-integratedClock rate x)) = 1-S T
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x _
    exact mul_nonneg (hn x) (Real.exp_pos _).le

theorem integratedClock_scale (rate : ℝ → ℝ) (a t : ℝ) :
    integratedClock (fun x => a*rate x) t = a * integratedClock rate t := by
  unfold integratedClock
  rw [intervalIntegral.integral_const_mul]

theorem pan_pair_three_survival_identity (rate : ℝ → ℝ)
    (hRate : LocallyIntegrable rate volume) (hn : ∀ t, 0 ≤ rate t)
    {T : ℝ} (hT : 0 ≤ T) :
    1 - (panPairLaw (fun t => 3*rate t)).real (Ioc 0 T) =
      (1 - (panPairLaw rate).real (Ioc 0 T))^3 := by
  have h3 : LocallyIntegrable (fun t => 3*rate t) volume := by
    convert! hRate.smul (3 : ℝ) using 1
  rw [panPairLaw_real_Ioc _ h3 (fun t => mul_nonneg (by norm_num) (hn t)) hT,
    panPairLaw_real_Ioc rate hRate hn hT, integratedClock_scale]
  have he : Real.exp (-(3 * integratedClock rate T)) =
      Real.exp (-integratedClock rate T)^3 := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

end Rhone.Statistics.Identifiability
