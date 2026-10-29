/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingCountLaw

/-! # A measure-level product representation for ordered pan merger times -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.PanThreeSample

lemma pairDensity_aemeasurable (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume) :
    AEMeasurable (fun t => ENNReal.ofReal (rate t * Real.exp (-integratedClock rate t)))
      (volume.restrict (Ioi 0)) := by
  have hE : Continuous (fun t => Real.exp (-integratedClock rate t)) :=
    Real.continuous_exp.comp (integratedClock_continuous rate hr).neg
  exact (hr.aestronglyMeasurable.aemeasurable.mul
    hE.measurable.aemeasurable).ennreal_ofReal.restrict

theorem law_product_representation (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) :
    law rate = (ENNReal.ofReal (3 / 2 : ℝ) •
      ((panPairLaw (fun u => 2 * rate u)).prod (panPairLaw rate))).restrict upperWedge := by
  have h2 : LocallyIntegrable (fun u => 2 * rate u) volume := by
    convert! hr.smul (2 : ℝ) using 1
  change law rate = (ENNReal.ofReal (3 / 2 : ℝ) •
    (((volume.restrict (Ioi 0)).withDensity (fun t =>
      ENNReal.ofReal (2 * rate t * Real.exp (-integratedClock (fun u => 2 * rate u) t)))).prod
      ((volume.restrict (Ioi 0)).withDensity (fun t =>
        ENNReal.ofReal (rate t * Real.exp (-integratedClock rate t)))))).restrict upperWedge
  rw [prod_withDensity₀ (pairDensity_aemeasurable _ h2) (pairDensity_aemeasurable rate hr),
    Measure.restrict_smul, restrict_withDensity upperWedge_open.measurableSet,
    Measure.prod_restrict, Measure.restrict_restrict upperWedge_open.measurableSet]
  have hsub : upperWedge ⊆ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) :=
    fun p hp => ⟨hp.1, hp.1.trans hp.2⟩
  rw [inter_eq_left.mpr hsub, ← withDensity_smul' _ _ (ENNReal.ofReal_ne_top)]
  unfold law triangularDensityLaw
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p _
  change ENNReal.ofReal (jointDensity rate p) =
    ENNReal.ofReal (3 / 2 : ℝ) *
      (ENNReal.ofReal (2 * rate p.1 * Real.exp (-integratedClock (fun u => 2 * rate u) p.1)) *
        ENNReal.ofReal (rate p.2 * Real.exp (-integratedClock rate p.2)))
  rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) (hn p.1))
    (Real.exp_pos _).le), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 2),
    integratedClock_scale, jointDensity_exp]
  congr 1
  rw [show -2 * integratedClock rate p.1 - integratedClock rate p.2 =
    -(2 * integratedClock rate p.1) + -integratedClock rate p.2 by ring, Real.exp_add]
  ring

end Rhone.Statistics.Identifiability.PanThreeSample
