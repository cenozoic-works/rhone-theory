/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableExposureOnset

/-! # A continuous strictly positive weight preserves every positive locally L1 exposure -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

lemma continuous_weighted_exposure_positive (f w : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) (hw : Continuous w) {a b : ℝ} (hab : a ≤ b)
    (hfn : ∀ᵐ u, u ∈ Icc a b → 0 ≤ f u)
    (hwp : ∀ u ∈ Icc a b, 0 < w u) (hpos : 0 < ∫ u in a..b, f u) :
    0 < ∫ u in a..b, f u * w u := by
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hw.continuousOn
  have hi : IntervalIntegrable f volume a b := locallyIntegrable_interval f hf a b
  have hle : (∫ v in a..b, f v * w u) ≤ ∫ v in a..b, f v * w v := by
    apply intervalIntegral.integral_mono_ae_restrict hab (hi.mul_const (w u))
      (hi.mul_continuousOn hw.continuousOn)
    filter_upwards [hfn.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Icc] with v hv hmem
    exact mul_le_mul_of_nonneg_left (hmin hmem) (hv hmem)
  rw [intervalIntegral.integral_mul_const] at hle
  exact (mul_pos hpos (hwp u hu)).trans_le hle

end Rhone.Statistics.Identifiability
