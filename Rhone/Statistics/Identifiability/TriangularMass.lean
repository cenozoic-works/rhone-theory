/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RegularJointLaw
public import Rhone.Statistics.Identifiability.ConditionalClockLaw

/-! # Tonelli mass balance for the triangular conditional-clock construction -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem lintegral_upperWedge (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p in upperWedge, f p ∂planeVolume) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi s, f (s,t) := by
  rw [← lintegral_indicator upperWedge_open.measurableSet]
  change (∫⁻ p, upperWedge.indicator f p ∂(volume : Measure ℝ).prod volume) = _
  rw [lintegral_prod _ (hf.indicator upperWedge_open.measurableSet).aemeasurable,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs),← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : s < t <;> simp [upperWedge,hs,ht]
  · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
    have hz : (fun t => upperWedge.indicator f (s,t)) = fun _ => 0 := by
      funext t
      simp [upperWedge,hs]
    rw [hz,lintegral_zero]

theorem triangular_clock_mass (b rate H : ℝ → ℝ)
    (hb : Measurable b) (hr : Measurable rate) (hH : Measurable H)
    (hn : ∀ t, 0 ≤ t → 0 ≤ b t)
    (hkernel : ∀ s, 0 ≤ s →
      (∫⁻ t in Ioi s, ENNReal.ofReal (conditionalPairDensity rate H s t)) = 1) :
    triangularDensityLaw (fun p => b p.1*conditionalPairDensity rate H p.1 p.2) univ =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (b s) := by
  rw [triangularDensityLaw,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (b p.1*conditionalPairDensity rate H p.1 p.2)) := by
    unfold conditionalPairDensity
    exact ((hb.comp measurable_fst).mul
      ((hr.comp measurable_snd).mul
        (((hH.comp measurable_fst).sub (hH.comp measurable_snd)).exp))).ennreal_ofReal
  rw [lintegral_upperWedge _ hm]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp_rw [ENNReal.ofReal_mul (hn s hs.le)]
  rw [lintegral_const_mul',hkernel s hs.le,mul_one]
  exact ENNReal.ofReal_ne_top

end Rhone.Statistics.Identifiability
