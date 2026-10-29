/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialNoiseLaw
public import Rhone.Coalescent.FiniteIntervalMaterialClock
public import Mathlib.Probability.Distributions.Exponential

/-! # Independent sampler coordinates and its exponential clock law -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory

theorem noiseLaw_coordinates :
    noiseLaw.map (fun u => (u 0, u 1, u 2)) =
      unitUniform.prod (unitUniform.prod unitUniform) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have he : noiseLaw.map e = unitUniform.prod (Measure.pi (fun _ : Fin 2 => unitUniform)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => unitUniform) (0 : Fin 3)).map_eq
  have htwo := (measurePreserving_finTwoArrow unitUniform).map_eq
  calc
    noiseLaw.map (fun u => (u 0, u 1, u 2)) =
        (noiseLaw.map e).map (Prod.map id MeasurableEquiv.finTwoArrow) := by
      rw [Measure.map_map (measurable_id.prodMap MeasurableEquiv.finTwoArrow.measurable)
        e.measurable]
      rfl
    _ = unitUniform.prod (unitUniform.prod unitUniform) := by
      rw [he, ← Measure.map_prod_map _ _ measurable_id MeasurableEquiv.finTwoArrow.measurable,
        Measure.map_id, htwo]

theorem inverseClock_law (r : ℝ) (hr : 0 < r) :
    unitUniform.map (fun u => -Real.log u / r) = ProbabilityTheory.expMeasure r := by
  have := isProbabilityMeasure_expMeasure hr
  have hm : Measurable (fun u : ℝ => -Real.log u / r) := by fun_prop
  have : IsProbabilityMeasure (unitUniform.map (fun u => -Real.log u / r)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply Measure.ext_of_Iic
  intro x
  rw [inverseClock_cdf r hr x, ← ofReal_cdf, cdf_expMeasure_eq hr]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx]
    have h : 1 ≤ Real.exp (-(r * x)) := Real.one_le_exp_iff.mpr (by nlinarith)
    rw [ENNReal.ofReal_zero]
    exact ENNReal.ofReal_eq_zero.mpr (by linarith)

end Rhone.Coalescent.SmcSupport
