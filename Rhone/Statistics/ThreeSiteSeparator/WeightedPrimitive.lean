/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.KernelPrimitive
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Continuous weighted primitives for the exact CDF energy identity -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

def weightedPrimitive (r : ℕ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, t^r * F t

lemma weightedPrimitive_deriv (r : ℕ) {F : ℝ → ℝ} (hF : Continuous F) (x : ℝ) :
    HasDerivAt (weightedPrimitive r F) (x^r * F x) x := by
  have hc : Continuous (fun t : ℝ => t^r * F t) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

@[fun_prop]
lemma weightedPrimitive_continuous (r : ℕ) {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous (weightedPrimitive r F) :=
  continuous_iff_continuousAt.mpr fun x => (weightedPrimitive_deriv r hF x).continuousAt

lemma weightedPrimitive_zero (r : ℕ) (F : ℝ → ℝ) : weightedPrimitive r F 0 = 0 := by
  simp [weightedPrimitive]

lemma weightedPrimitive_add (r : ℕ) {F G : ℝ → ℝ} (hF : Continuous F)
    (hG : Continuous G) (x : ℝ) :
    weightedPrimitive r (fun t => F t + G t) x =
      weightedPrimitive r F x + weightedPrimitive r G x := by
  unfold weightedPrimitive
  simp_rw [mul_add]
  apply intervalIntegral.integral_add
  · exact (show Continuous (fun t : ℝ => t^r * F t) by fun_prop).intervalIntegrable _ _
  · exact (show Continuous (fun t : ℝ => t^r * G t) by fun_prop).intervalIntegrable _ _

lemma weightedPrimitive_id (r : ℕ) (x : ℝ) :
    weightedPrimitive r (fun t => t) x = x^(r + 2) / (r + 2 : ℝ) := by
  unfold weightedPrimitive
  simp_rw [← pow_succ]
  rw [integral_pow]
  norm_num [Nat.cast_add, Nat.add_assoc]
  ring

lemma weightedPrimitive_centered (r : ℕ) {F : ℝ → ℝ} (hF : Continuous F) (x : ℝ) :
    weightedPrimitive r F x = weightedPrimitive r (fun t => F t - t) x +
      x^(r + 2) / (r + 2 : ℝ) := by
  have hc : Continuous (fun t : ℝ => F t - t) := hF.sub continuous_id
  have hi : Continuous (fun t : ℝ => t) := continuous_id
  have he := weightedPrimitive_add r hc hi x
  simp only [sub_add_cancel, weightedPrimitive_id] at he
  exact he

end Rhone.Statistics.ThreeSiteSeparator
