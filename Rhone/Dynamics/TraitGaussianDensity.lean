/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# An exact unnormalized density identity for Gaussian stabilizing trait selection

Source: lande1975, p. 225, eq. 2–4. -/

@[expose] public section
namespace Rhone.Dynamics.TraitBalance
open ProbabilityTheory
open scoped NNReal

/-- Source: lande1975, p. 225, eq. 2–4. -/
theorem weighted_gaussian_density (V S : ℝ≥0) (hV : 0 < V) (hS : 0 < S) (z : ℝ) :
    gaussianPDFReal 0 V z * Real.exp (-z^2/(2*(S : ℝ))) =
      Real.sqrt ((S : ℝ)/((V : ℝ)+(S : ℝ))) * gaussianPDFReal 0 (V*S/(V+S)) z := by
  have hv : 0 < (V : ℝ) := NNReal.coe_pos.mpr hV
  have hs : 0 < (S : ℝ) := NNReal.coe_pos.mpr hS
  have hd : 0 < (V : ℝ)+(S : ℝ) := by positivity
  have hw : 0 < (V : ℝ)*(S : ℝ)/((V : ℝ)+(S : ℝ)) := by positivity
  have hc : 0 < Real.sqrt ((S : ℝ)/((V : ℝ)+(S : ℝ))) := by positivity
  have hr : 0 < Real.sqrt (2*Real.pi*(V : ℝ)) := by positivity
  have hroot : Real.sqrt (2*Real.pi*((V : ℝ)*(S : ℝ)/((V : ℝ)+(S : ℝ)))) =
      Real.sqrt ((S : ℝ)/((V : ℝ)+(S : ℝ))) * Real.sqrt (2*Real.pi*(V : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (S : ℝ)/((V : ℝ)+(S : ℝ)))]
    congr 1
    ring
  have hcoeff : (Real.sqrt (2*Real.pi*(V : ℝ)))⁻¹ =
      Real.sqrt ((S : ℝ)/((V : ℝ)+(S : ℝ))) *
        (Real.sqrt (2*Real.pi*((V : ℝ)*(S : ℝ)/((V : ℝ)+(S : ℝ)))))⁻¹ := by
    rw [hroot]
    field_simp
  have hexp : -z^2/(2*(V : ℝ)) + -z^2/(2*(S : ℝ)) =
      -z^2/(2*((V : ℝ)*(S : ℝ)/((V : ℝ)+(S : ℝ)))) := by
    field_simp
    ring
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add]
  rw [mul_assoc, ← Real.exp_add, hexp, hcoeff]
  ring

end Rhone.Dynamics.TraitBalance
