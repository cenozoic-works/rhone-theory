/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FoldedCounts.ScalarModel

/-! # Duration measures and the branch-length-preserving exponential swap -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal
namespace Rhone.Statistics.FoldedCounts
open MarkovChain.Identifiability Identifiability

def exponential (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (a * Real.exp (-a * t)))

lemma exponential_probability {a : ℝ} (ha : 0 < a) : IsProbabilityMeasure (exponential a) := by
  constructor
  simpa [exponential, ExponentialTwoEvent.shiftedDensity] using
    ExponentialTwoEvent.shifted_lintegral ha 0

lemma exponential_product_ordered {a b : ℝ} (ha : 0 < a) :
    ((exponential a).prod (exponential b)).map PanThreeSample.toOrdered =
      ExponentialTwoEvent.law a b := by
  change ((exponential a).prod (exponential b)).map upperShear = _
  rw [exponential, exponential, shear_product_density _ _ (by fun_prop) (by fun_prop)]
  unfold ExponentialTwoEvent.law triangularDensityLaw
  congr 1
  funext p
  rw [← ENNReal.ofReal_mul (mul_nonneg ha.le (Real.exp_pos _).le)]
  simp [ExponentialTwoEvent.density, ExponentialTwoEvent.shiftedDensity]

lemma scalar_duration_law (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (scalarModel a b ha hb).durationLaw = (exponential a).prod (exponential b) := by
  rw [FinitePhase.Model.durationLaw, scalar_law, ← exponential_product_ordered ha,
    Measure.map_map PanThreeSample.measurable_toDurations PanThreeSample.measurable_toOrdered]
  have he : PanThreeSample.toDurations ∘ PanThreeSample.toOrdered = id := by
    funext p
    simp [PanThreeSample.toDurations, PanThreeSample.toOrdered]
  rw [he, Measure.map_id]

lemma positive_volume_map_mul {c : ℝ} (hc : 0 < c) :
    (volume.restrict (Ioi (0 : ℝ))).map (fun t => c * t) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
  have he : (fun t : ℝ => c * t) ⁻¹' Ioi 0 = Ioi 0 := by
    ext t
    exact mul_pos_iff_of_pos_left hc
  conv_lhs => rw [← he]
  rw [← Measure.restrict_map (f := fun t : ℝ => c * t)
    (measurable_const.mul measurable_id) measurableSet_Ioi,
    Real.map_volume_mul_left hc.ne', Measure.restrict_smul, abs_of_pos (inv_pos.mpr hc)]

lemma exponential_map_mul {c : ℝ} (hc : 0 < c) (a : ℝ) :
    (exponential a).map (fun t => c * t) = exponential (a / c) := by
  change (exponential a).map (MeasurableEquiv.mulLeft₀ c hc.ne') = _
  rw [exponential, equiv_map_withDensity _ _ _ (by fun_prop)]
  simp only [MeasurableEquiv.symm_mulLeft₀, MeasurableEquiv.coe_mulLeft₀]
  rw [positive_volume_map_mul hc, withDensity_smul_measure,
    ← withDensity_smul' _ _ (by simp)]
  congr 1
  funext t
  change ENNReal.ofReal c⁻¹ * ENNReal.ofReal (a * Real.exp (-a * (c⁻¹ * t))) = _
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  congr 1
  rw [show -a * (c⁻¹ * t) = -(a / c) * t by ring]
  ring

def durationSwap (p : ℝ × ℝ) : ℝ × ℝ := ((2 / 3) * p.2, (3 / 2) * p.1)

lemma measurable_durationSwap : Measurable durationSwap := by unfold durationSwap; fun_prop

lemma source_duration_swap : comparator.durationLaw.map durationSwap = source.durationLaw := by
  rw [comparator, source, scalar_duration_law, scalar_duration_law]
  let : IsProbabilityMeasure (exponential 3) := exponential_probability (by norm_num)
  let : IsProbabilityMeasure (exponential 1) := exponential_probability (by norm_num)
  have he : durationSwap = (Prod.map (fun t : ℝ => (2 / 3) * t)
      (fun t : ℝ => (3 / 2) * t)) ∘ Prod.swap := rfl
  rw [he, ← Measure.map_map (by fun_prop) measurable_swap, Measure.prod_swap,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    exponential_map_mul (by norm_num : (0 : ℝ) < 2 / 3),
    exponential_map_mul (by norm_num : (0 : ℝ) < 3 / 2)]
  norm_num

def totalLength (p : ℝ × ℝ) : ℝ := 3 * p.1 + 2 * p.2

lemma measurable_totalLength : Measurable totalLength := by unfold totalLength; fun_prop

lemma totalLength_swap (p : ℝ × ℝ) : totalLength (durationSwap p) = totalLength p := by
  unfold totalLength durationSwap
  ring

theorem source_totalLength_law :
    source.durationLaw.map totalLength = comparator.durationLaw.map totalLength := by
  rw [← source_duration_swap, Measure.map_map measurable_totalLength measurable_durationSwap]
  congr 1
  exact funext totalLength_swap

lemma comparator_pan_law : comparator.law = PanThreeSample.law (fun _ => 1) := by
  rw [comparator, scalar_law]
  unfold ExponentialTwoEvent.law PanThreeSample.law
  congr 1
  funext p
  rw [PanThreeSample.jointDensity_exp]
  simp only [ExponentialTwoEvent.density, ExponentialTwoEvent.shiftedDensity,
    integratedClock, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, one_mul]
  rw [show 3 * Real.exp (-3 * p.1) * Real.exp (-1 * (p.2 - p.1)) =
      3 * (Real.exp (-3 * p.1) * Real.exp (-1 * (p.2 - p.1))) by ring,
    ← Real.exp_add]
  congr 2
  ring

lemma comparator_pan_duration :
    comparator.durationLaw = PanThreeSample.durationLaw (fun _ => 1) := by
  rw [FinitePhase.Model.durationLaw, comparator_pan_law, PanThreeSample.durationLaw]

end Rhone.Statistics.FoldedCounts
