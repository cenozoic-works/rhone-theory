/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TwoEpochMoments
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The two-epoch clock-time size function and its exact Laplace integral -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable def twoEpochSize (u v τ t : ℝ) : ℝ :=
  u + (Ioi τ).indicator (fun _ => v-u) t

theorem twoEpochSize_pos {u v τ : ℝ} (hu : 0 < u) (hv : 0 < v) (t : ℝ) :
    0 < twoEpochSize u v τ t := by
  unfold twoEpochSize
  by_cases ht : t ∈ Ioi τ
  · simpa only [indicator_of_mem ht, add_sub_cancel] using hv
  · simpa only [indicator_of_notMem ht, add_zero] using hu

theorem twoEpochSize_weight (u v τ α t : ℝ) :
    twoEpochSize u v τ t * Real.exp (-α*t) =
      u * Real.exp (-α*t) + (Ioi τ).indicator (fun x => (v-u)*Real.exp (-α*x)) t := by
  unfold twoEpochSize
  by_cases ht : t ∈ Ioi τ
  · simp only [indicator_of_mem ht]
    ring
  · simp only [indicator_of_notMem ht, add_zero]

theorem twoEpoch_weight_integrable {u v τ α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t => twoEpochSize u v τ t * Real.exp (-α*t)) (Ioi 0) := by
  have hi := integrableOn_exp_mul_Ioi (a := -α) (by linarith) 0
  simp_rw [twoEpochSize_weight]
  exact (hi.const_mul u).add ((hi.const_mul (v-u)).indicator measurableSet_Ioi)

theorem twoEpoch_laplace {u v τ α : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) :
    (∫ t in Ioi (0 : ℝ), twoEpochSize u v τ t * Real.exp (-α*t)) =
      (u*(1-Real.exp (-α*τ))+v*Real.exp (-α*τ))/α := by
  have hi := integrableOn_exp_mul_Ioi (a := -α) (by linarith) 0
  have hiu := hi.const_mul u
  have hiv := (hi.const_mul (v-u)).indicator (s := Ioi τ) measurableSet_Ioi
  simp_rw [twoEpochSize_weight]
  rw [integral_add hiu hiv, integral_const_mul, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have hs : Ioi τ ∩ Ioi (0 : ℝ) = Ioi τ := inter_eq_left.mpr (fun _ hx => lt_of_le_of_lt hτ hx)
  rw [hs, integral_const_mul, integral_exp_mul_Ioi (by linarith),
    integral_exp_mul_Ioi (by linarith)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

end Rhone.Statistics.Identifiability
