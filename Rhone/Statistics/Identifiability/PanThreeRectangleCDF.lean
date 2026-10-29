/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanThreeFactorization
public import Rhone.Statistics.Identifiability.PanPairTailProbability

/-! # Exact probability-rectangle identities for proper pan histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability.PanThreeSample

theorem law_real_prefix_tail (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (law rate).real (Ioc 0 s ×ˢ Ioi t) =
      (3 / 2 : ℝ) * (1 - Real.exp (-2 * integratedClock rate s)) *
        Real.exp (-integratedClock rate t) := by
  have h2 : LocallyIntegrable (fun u => 2 * rate u) volume := by
    convert! hr.smul (2 : ℝ) using 1
  let : IsProbabilityMeasure (panPairLaw rate) := pairLaw_probability rate hr hn htail
  have hsub : Ioc 0 s ×ˢ Ioi t ⊆ upperWedge := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans_lt (hst.trans_lt hp.2)⟩
  rw [law_product_representation rate hr hn,
    measureReal_restrict_apply (measurableSet_Ioc.prod measurableSet_Ioi),
    inter_eq_left.mpr hsub, measureReal_ennreal_smul_apply, measureReal_prod_prod,
    panPairLaw_real_Ioc _ h2 (fun u => mul_nonneg (by norm_num) (hn u)) hs,
    pairLaw_real_Ioi rate hr hn htail (hs.trans hst), integratedClock_scale,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  rw [neg_mul]
  ring

theorem law_real_prefix_tail_clock (rate : ℝ → ℝ) (hr : LocallyIntegrable rate volume)
    (hn : ∀ t, 0 ≤ rate t) (htail : Tendsto (integratedClock rate) atTop atTop)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (law rate).real (Ioc 0 s ×ˢ Ioi t) =
      (3 / 2 : ℝ) * Real.exp (-integratedClock rate t) *
        (1 - (Real.exp (-integratedClock rate s))^2) := by
  rw [law_real_prefix_tail rate hr hn htail hs hst]
  have he : Real.exp (-2 * integratedClock rate s) =
      (Real.exp (-integratedClock rate s))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  ring

end Rhone.Statistics.Identifiability.PanThreeSample
