/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.EnergyIntegrals

/-! # Exact continuous-CDF energy identity, before any probabilistic bridge -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma integrated_cubic_centered {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ x in (0 : ℝ)..1, (F x)^2*weight F x) =
      -2988 - 59760*(∫ x in (0 : ℝ)..1, x^8*(F x - x)) +
        (∫ x in (0 : ℝ)..1, x^2*weight (fun t => F t - t) x) +
        (∫ x in (0 : ℝ)..1, 2*x*(F x - x)*weight (fun t => F t - t) x) +
        (∫ x in (0 : ℝ)..1, (F x - x)^2*weight F x) := by
  have hH : Continuous (fun t : ℝ => F t - t) := hF.sub continuous_id
  have h0 : Continuous (fun x : ℝ => -29880*x^9) := by fun_prop
  have h1 : Continuous (fun x : ℝ => 59760*x^8*(F x - x)) := by fun_prop
  have h2 : Continuous (fun x : ℝ => x^2*weight (fun t => F t - t) x) := by fun_prop
  have h3 : Continuous (fun x : ℝ => 2*x*(F x - x)*weight (fun t => F t - t) x) := by
    fun_prop
  have h4 : Continuous (fun x : ℝ => (F x - x)^2*weight F x) := by fun_prop
  have hi01 : IntervalIntegrable (fun x : ℝ => -29880*x^9 - 59760*x^8*(F x - x))
      volume 0 1 := (show Continuous _ by fun_prop).intervalIntegrable _ _
  have hi012 : IntervalIntegrable (fun x : ℝ => -29880*x^9 - 59760*x^8*(F x - x) +
      x^2*weight (fun t => F t - t) x) volume 0 1 :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  have hi0123 : IntervalIntegrable (fun x : ℝ => -29880*x^9 - 59760*x^8*(F x - x) +
      x^2*weight (fun t => F t - t) x +
      2*x*(F x - x)*weight (fun t => F t - t) x) volume 0 1 :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  simp_rw [cubic_integrand_centered hF]
  rw [intervalIntegral.integral_add hi0123
      (h4.intervalIntegrable _ _),
    intervalIntegral.integral_add hi012
      (h3.intervalIntegrable _ _),
    intervalIntegral.integral_add hi01 (h2.intervalIntegrable _ _),
    intervalIntegral.integral_sub (h0.intervalIntegrable _ _) (h1.intervalIntegrable _ _)]
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  norm_num [integral_pow]

theorem cdf_energy_identity {F : ℝ → ℝ} (hF : Continuous F) :
    cdfFunctional F + 384 -
      boundary (weightedPrimitive 1 (fun t => F t - t) 1)
        (weightedPrimitive 3 (fun t => F t - t) 1)
        (weightedPrimitive 5 (fun t => F t - t) 1) =
      (∫ x in (0 : ℝ)..1, (F x - x)^2*weight F x) -
        627480*(∫ x in (0 : ℝ)..1, x^3*(weightedPrimitive 1 (fun t => F t - t) x)^2) := by
  have hH : Continuous (fun t : ℝ => F t - t) := hF.sub continuous_id
  rw [functional_centered_constants hF, integrated_cubic_centered hF,
    integrated_linear_weight hH, integrated_quadratic_weight hH]
  ring

end Rhone.Statistics.ThreeSiteSeparator
