/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.FunProp

/-! # Supported pair-time Laplace bounds used by the observer bridge -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.PairObservationChannel

noncomputable def pairLaplace (μ : Measure ℝ) (k : ℝ) : ℝ :=
  ∫ t, Real.exp (-k*t) ∂μ

theorem exp_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] {k : ℝ}
    (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) : Integrable (fun t => Real.exp (-k*t)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) ht)

theorem pair_laplace_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ] {k : ℝ}
    (hk : 0 ≤ k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) :
    0 ≤ pairLaplace μ k ∧ pairLaplace μ k ≤ 1 := by
  constructor
  · exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  · have h := integral_mono_ae (exp_integrable μ hk hμ) (integrable_const (1 : ℝ))
      (hμ.mono (fun t ht => Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) ht)))
    simpa [pairLaplace] using h

end Rhone.Statistics.PairObservationChannel
