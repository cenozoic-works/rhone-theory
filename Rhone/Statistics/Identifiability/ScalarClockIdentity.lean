/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegratedClock
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exact scalar survival under a continuous time-dependent hazard -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

lemma scalar_survival_clock_identity (a g : ℝ → ℝ) (ha : Continuous a)
    (hg : ∀ u, HasDerivAt g (-a u * g u) u) (s t : ℝ) :
    g t = g s * Real.exp (integratedClock a s - integratedClock a t) := by
  have hH (u : ℝ) : HasDerivAt (integratedClock a) (a u) u :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable 0 u)
      ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have he (u : ℝ) : HasDerivAt (fun v => Real.exp (integratedClock a v))
      (Real.exp (integratedClock a u) * a u) u := by
    have hExp : HasDerivAt Real.exp (Real.exp (integratedClock a u)) (integratedClock a u) :=
      Real.hasDerivAt_exp _
    convert! hExp.comp u (hH u) using 1
  have hd (u : ℝ) : HasDerivAt (fun v => Real.exp (integratedClock a v) * g v) 0 u :=
    ((he u).mul (hg u)).congr_deriv (by ring)
  have hconst := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t s
  have hExp : Real.exp (integratedClock a t) *
      Real.exp (integratedClock a s - integratedClock a t) = Real.exp (integratedClock a s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply mul_left_cancel₀ (Real.exp_ne_zero (integratedClock a t))
  calc
    _ = Real.exp (integratedClock a s) * g s := hconst
    _ = _ := by rw [← hExp]; ring

end Rhone.Statistics.Identifiability
