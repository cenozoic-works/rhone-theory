/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ProfileFirstMarginal

/-! # Every proper locally-L1 pan history supplies the observable first-survival regularity -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership

noncomputable def panProfile (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    FirstSurvivalProfile := by
  let F := fun t => Real.exp (-3 * integratedClock rate t)
  have hcont : Continuous F :=
    Real.continuous_exp.comp (continuous_const.mul (integratedClock_continuous rate hr))
  have hD : LocallyIntegrable (PanThreeSample.firstDensity rate) volume := by
    have h3 : LocallyIntegrable (fun t => 3 * rate t) volume := by
      convert! hr.smul (3 : ℝ) using 1
    exact h3.mul_continuous hcont
  refine
    { survival := F
      density := PanThreeSample.firstDensity rate
      continuous_survival := hcont
      initial := ?_
      positive := ?_
      ac := ?_
      density_locallyIntegrable := hD.locallyIntegrableOn _
      density_nonnegative := ?_
      derivative_ae := ?_
      proper := ?_ }
  · simp [F, integratedClock]
  · intro t _
    exact Real.exp_pos _
  · intro T _
    exact ac_exp ((integratedClock_ac_zero rate hr T).const_mul (-3))
  · exact ae_of_all _ fun t _ =>
      mul_nonneg (mul_nonneg (by norm_num) (hn t)) (Real.exp_pos _).le
  · filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hr] with t ht _
    have hclock : HasDerivAt (integratedClock rate) (rate t) t := ht 0
    convert! (hclock.const_mul (-3)).exp using 1
    dsimp only [PanThreeSample.firstDensity]
    ring
  · apply Real.tendsto_exp_atBot.comp
    simpa only [neg_mul, Function.comp_def] using tendsto_neg_atTop_atBot.comp
      (htail.const_mul_atTop (by norm_num : (0 : ℝ) < 3))

lemma panProfile_matches (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop) :
    (panProfile rate hr hn htail).Matches (PanThreeSample.law rate) := by
  intro t ht
  exact PanThreeSample.first_survival rate hr hn htail ht

end Rhone.Statistics.Identifiability.ThreeSampleMembership
