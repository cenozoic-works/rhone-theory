/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PairObservationChannel.LaplaceKernel

/-! # Strict Laplace interval for proper strictly positive finite pair times -/

@[expose] public section

open MeasureTheory
namespace Rhone.Statistics.GeneralPairTimePower
open PairObservationChannel

theorem laplace_strict_interval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℝ} (hk : 0 < k) (hμ : ∀ᵐ t ∂μ, 0 < t) :
    0 < pairLaplace μ k ∧ pairLaplace μ k < 1 := by
  have hs := hμ.mono (fun _ h => h.le)
  have hi := exp_integrable μ hk.le hs
  constructor
  · exact integral_exp_pos hi
  · have hb := (pair_laplace_bounds μ hk.le hs).2
    apply lt_of_le_of_ne hb
    intro he
    have hle : (fun t => Real.exp (-k * t)) ≤ᵐ[μ] (fun _ => (1 : ℝ)) :=
      hs.mono (fun t ht => Real.exp_le_one_iff.mpr (by nlinarith))
    have heq := (integral_eq_iff_of_ae_le hi (integrable_const (1 : ℝ)) hle).mp
      (show (∫ t, Real.exp (-k * t) ∂μ) = ∫ _t, (1 : ℝ) ∂μ by simpa [pairLaplace] using he)
    obtain ⟨t, ht, heqt⟩ := (hμ.and heq).exists
    have hlt : Real.exp (-k * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith

end Rhone.Statistics.GeneralPairTimePower
