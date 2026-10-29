/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.WeightedPrimitive

/-! # The continuous joint-CDF formula and its one-variable integral -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

def cdfJointFunction (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (3*(F x)^2*F (min x y)-(F (min x y))^3)/2

lemma cdfJointFunction_continuous {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous (fun p : ℝ × ℝ => cdfJointFunction F p.1 p.2) := by
  unfold cdfJointFunction
  fun_prop

lemma cdfJointFunction_below (F : ℝ → ℝ) {x y : ℝ} (hyx : y ≤ x) :
    cdfJointFunction F x y = (3*(F x)^2*F y-(F y)^3)/2 := by
  rw [cdfJointFunction, min_eq_right hyx]

lemma cdfJointFunction_above (F : ℝ → ℝ) {x y : ℝ} (hxy : x ≤ y) :
    cdfJointFunction F x y = (F x)^3 := by
  rw [cdfJointFunction, min_eq_left hxy]
  ring

lemma cdfJointFunction_lower_integral {F : ℝ → ℝ} (hF : Continuous F) (q : ℕ)
    {x : ℝ} (hx : 0 ≤ x) :
    (∫ y in (0 : ℝ)..x, y^q*cdfJointFunction F x y) =
      (3/2 : ℝ)*(F x)^2*weightedPrimitive q F x -
        (1/2 : ℝ)*weightedPrimitive q (fun y => (F y)^3) x := by
  have he : (∫ y in (0 : ℝ)..x, y^q*cdfJointFunction F x y) =
      ∫ y in (0 : ℝ)..x, ((3/2 : ℝ)*(F x)^2)*(y^q*F y) - (1/2 : ℝ)*(y^q*(F y)^3) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx] at hy
    dsimp only
    rw [cdfJointFunction_below F hy.2]
    ring
  rw [he, intervalIntegral.integral_sub
    ((show Continuous (fun y : ℝ => ((3/2 : ℝ)*(F x)^2)*(y^q*F y)) by
      fun_prop).intervalIntegrable _ _)
    ((show Continuous (fun y : ℝ => (1/2 : ℝ)*(y^q*(F y)^3)) by
      fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rfl

lemma cdfJointFunction_upper_integral {F : ℝ → ℝ} (q : ℕ) {x : ℝ} (hx : x ≤ 1) :
    (∫ y in x..(1 : ℝ), y^q*cdfJointFunction F x y) =
      (F x)^3*(1-x^(q+1))/((q : ℝ)+1) := by
  have he : (∫ y in x..(1 : ℝ), y^q*cdfJointFunction F x y) =
      ∫ y in x..(1 : ℝ), (F x)^3*y^q := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx] at hy
    dsimp only
    rw [cdfJointFunction_above F hy.1, mul_comm]
  rw [he, intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow]
  ring

lemma cdfJointFunction_inner_integral {F : ℝ → ℝ} (hF : Continuous F) (q : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ y in (0 : ℝ)..1, y^q*cdfJointFunction F x y) =
      (3/2 : ℝ)*(F x)^2*weightedPrimitive q F x -
        (1/2 : ℝ)*weightedPrimitive q (fun y => (F y)^3) x +
        (F x)^3*(1-x^(q+1))/((q : ℝ)+1) := by
  have hc : Continuous (fun y : ℝ => y^q*cdfJointFunction F x y) := by
    unfold cdfJointFunction
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x 1),
    cdfJointFunction_lower_integral hF q hx.1, cdfJointFunction_upper_integral q hx.2]

end Rhone.Statistics.ThreeSiteSeparator
