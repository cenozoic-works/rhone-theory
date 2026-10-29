/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AELevelSetDerivative
public import Rhone.Statistics.Identifiability.ACComparisonBounds
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Absolute continuity and the almost-everywhere derivative of a positive part -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

lemma ac_positivePart {x : ℝ → ℝ} {a b : ℝ}
    (hx : AbsolutelyContinuousOnInterval x a b) (threshold : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => max (x t - threshold) 0) a b := by
  have hl : LipschitzWith 1 (fun z : ℝ => z - threshold) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right, le_refl]
  apply ac_comp_lipschitzOn x (fun z => max (z - threshold) 0) univ hx
  · exact (hl.max_const 0).lipschitzOnWith
  · intro t _
    exact mem_univ _

lemma halfLine_ac_ae_differentiable {f : ℝ → ℝ}
    (hf : ∀ b, 0 ≤ b → AbsolutelyContinuousOnInterval f 0 b) :
    ∀ᵐ t, 0 ≤ t → DifferentiableAt ℝ f t := by
  have h (n : ℕ) := (hf (n + 1) (by positivity)).ae_differentiableAt
  filter_upwards [ae_all_iff.mpr h] with t ht ht0
  obtain ⟨n, hn⟩ := exists_nat_gt t
  apply ht n
  rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ n + 1)]
  exact ⟨ht0, by linarith⟩

theorem ae_positivePart_derivative (x xDot : ℝ → ℝ) (threshold : ℝ)
    (hx : ∀ b, 0 ≤ b → AbsolutelyContinuousOnInterval x 0 b)
    (hxd : ∀ᵐ t, 0 ≤ t → HasDerivAt x (xDot t) t) :
    ∀ᵐ t, 0 ≤ t → HasDerivAt (fun u => max (x u - threshold) 0)
      (if threshold < x t then xDot t else 0) t := by
  let w := fun t => max (x t - threshold) 0
  have hwac b hb := ac_positivePart (hx b hb) threshold
  filter_upwards [hxd, halfLine_ac_ae_differentiable hwac,
    ae_derivative_zero_on_level w 0] with t hxt hwt hzero ht0
  have hdx := hxt ht0
  by_cases hpos : threshold < x t
  · rw [ite_eq_left hpos]
    apply (hdx.sub_const threshold).congr_of_eventuallyEq
    filter_upwards [hdx.continuousAt (Ioi_mem_nhds hpos)] with u hu
    exact max_eq_left (sub_nonneg.mpr hu.le)
  · rw [ite_eq_right hpos]
    rcases lt_or_eq_of_le (le_of_not_gt hpos) with hlt | heq
    · apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hdx.continuousAt (Iio_mem_nhds hlt)] with u hu
      exact max_eq_right (sub_nonpos.mpr hu.le)
    · have hdw := (hwt ht0).hasDerivAt
      have hw0 : w t = 0 := by simp only [w, heq, sub_self, max_self]
      have hz := hzero hw0 _ hdw
      simpa only [hz] using hdw

end Rhone.Statistics.Identifiability
