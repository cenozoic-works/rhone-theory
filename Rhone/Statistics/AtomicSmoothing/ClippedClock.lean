/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.CDFRegularity
public import Rhone.Statistics.Identifiability.RegularPairSurvivalReconstruction

/-! # A globally Lipschitz version of exp(-t), equal to it on nonnegative time -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.AtomicSmoothing

def unitClock (t : ℝ) : ℝ := Real.exp (-max t 0)

lemma unitClock_zero : unitClock 0 = 1 := by simp [unitClock]
lemma unitClock_positive (t : ℝ) : 0 < unitClock t := Real.exp_pos _
lemma unitClock_le_one (t : ℝ) : unitClock t ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right _ _))
lemma unitClock_eq {t : ℝ} (ht : 0 ≤ t) : unitClock t = Real.exp (-t) := by
  rw [unitClock, max_eq_left ht]

lemma unitClock_antitone : Antitone unitClock := by
  intro s t hst
  exact Real.exp_le_exp.mpr (neg_le_neg (max_le_max hst le_rfl))

lemma negative_exp_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
  convert! (hasDerivAt_id t).neg.exp using 1
  dsimp
  ring

lemma negative_exp_lipschitzOn :
    LipschitzOnWith 1 (fun t : ℝ => Real.exp (-t)) (Ici (0 : ℝ)) := by
  apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (negative_exp_hasDerivAt t).hasDerivWithinAt)
  intro t ht
  apply NNReal.coe_le_coe.mp
  change ‖-Real.exp (-t)‖ ≤ (1 : ℝ)
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)

lemma unitClock_lipschitz : LipschitzWith 1 unitClock := by
  have hmax : LipschitzWith 1 (fun t : ℝ => max t 0) := LipschitzWith.id.max_const 0
  have hc : LipschitzOnWith (1 * 1) unitClock univ :=
    negative_exp_lipschitzOn.comp hmax.lipschitzOnWith (fun t _ => le_max_right t 0)
  simpa only [one_mul, lipschitzOnWith_univ] using hc

lemma unitClock_tendsto : Tendsto unitClock atTop (𝓝 (0 : ℝ)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  apply he.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (unitClock_eq ht).symm

lemma lipschitz_deriv_locallyIntegrable {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    LocallyIntegrable (deriv f) volume := by
  intro x
  refine ⟨Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  have hac : AbsolutelyContinuousOnInterval f (x-1) (x+1) :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp
    hac.intervalIntegrable_deriv

end Rhone.Statistics.AtomicSmoothing
