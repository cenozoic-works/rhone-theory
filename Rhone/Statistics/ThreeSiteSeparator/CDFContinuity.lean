/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith

/-! # Continuity of the real CDF of an atomless finite law -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma realCDF_continuous (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Continuous (fun x : ℝ => μ.real (Iic x)) := by
  have he : (fun x : ℝ => ∫ y in Iic x, (1 : ℝ) ∂μ) = fun x => μ.real (Iic x) := by
    funext x
    rw [setIntegral_const, smul_eq_mul, mul_one]
  rw [← he]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic (x+1)) μ :=
    (integrable_const 1).integrableOn
  exact hi.continuousOn_Iic_primitive_Iic.continuousAt (Iic_mem_nhds (by linarith))

end Rhone.Statistics.ThreeSiteSeparator
