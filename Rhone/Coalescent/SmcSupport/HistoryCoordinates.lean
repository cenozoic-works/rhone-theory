/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.DensityTransport
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-! # Clock and breakpoint pushforwards in chronological real coordinates -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

private theorem expMeasure_density (q : ℝ) : expMeasure q =
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun t => ENNReal.ofReal (q * Real.exp (-q * t))) := by
  change volume.withDensity (exponentialPDF q) = _
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
  rw [exponentialPDF_eq]
  by_cases hp : 0 < x
  · simp [Set.indicator_of_mem, hp, hp.le, neg_mul]
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simp [Set.indicator_of_notMem, hp, not_le.mpr hn]

theorem inverseClock_shift_density (q : ℝ) (hq : 0 < q) (s : ℝ) :
    Rhone.Coalescent.IntervalProcess.unitUniform.map (fun u => s - Real.log u / q) =
      (volume.restrict (Set.Ioi s)).withDensity
        (fun t => ENNReal.ofReal (q * Real.exp (-q * (t - s)))) := by
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.addLeft s
  have he : (volume.restrict (Set.Ioi (0 : ℝ))).map e =
      volume.restrict (Set.Ioi s) := by
    have hp : e ⁻¹' Set.Ioi s = Set.Ioi (0 : ℝ) := by
      ext x
      simp [e]
    rw [← hp, ← e.restrict_map]
    have hm : volume.map e = volume := (measurePreserving_add_left volume s).map_eq
    rw [hm]
  calc
    _ = (Rhone.Coalescent.IntervalProcess.unitUniform.map
        (fun u => -Real.log u / q)).map e := by
      rw [Measure.map_map e.measurable (by fun_prop)]
      congr 1
      ext u
      simp [e, sub_eq_add_neg, neg_div]
    _ = _ := by
      rw [inverseClock_law q hq, expMeasure_density, map_withDensity_equiv e _ _ (by fun_prop), he]
      congr 2
      ext t
      simp [e, sub_eq_add_neg, add_comm]

theorem affineCut_uniform_law (lo hi : ℝ) (hlt : lo < hi) :
    unitUniform.map (fun u => lo + (hi - lo) * u) =
      ENNReal.ofReal ((hi - lo)⁻¹) • volume.restrict (Set.Ioo lo hi) := by
  have hc : 0 < hi - lo := sub_pos.mpr hlt
  let e : ℝ ≃ᵐ ℝ := (MeasurableEquiv.mulLeft₀ (hi - lo) hc.ne').trans
    (MeasurableEquiv.addLeft lo)
  have hp : e ⁻¹' Set.Ioo lo hi = Set.Ioo (0 : ℝ) 1 := by
    ext u
    change (lo < lo + (hi - lo) * u ∧ lo + (hi - lo) * u < hi) ↔ (0 < u ∧ u < 1)
    constructor
    · intro h
      constructor <;> nlinarith
    · intro h
      constructor <;> nlinarith
  have hm : volume.map e = ENNReal.ofReal ((hi - lo)⁻¹) • volume := by
    change volume.map ((fun u => lo + u) ∘ (fun u => (hi - lo) * u)) = _
    rw [← Measure.map_map (measurable_const_add _) (measurable_const_mul _),
      Real.map_volume_mul_left hc.ne', Measure.map_smul,
      (measurePreserving_add_left volume lo).map_eq, abs_of_pos (inv_pos.mpr hc)]
    exact (measurable_const_add lo).aemeasurable
  change (volume.restrict (Set.Ioo (0 : ℝ) 1)).map e = _
  rw [← hp, ← e.restrict_map, hm, Measure.restrict_smul]

end Rhone.Coalescent.SmcSupport
