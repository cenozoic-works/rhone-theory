/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ACComparisonBounds

/-! # A scalar obstruction needed for the arbitrary-initial-sampling extension -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling

theorem proper_clock_forces_one (x w wDot H rate : ℝ → ℝ) (threshold : ℝ)
    (hthreshold : threshold < 1)
    (hx : ∀ t, 0 ≤ t → x t ≤ 1)
    (hw : ∀ t, 0 ≤ t → w t = max (x t - threshold) 0)
    (hwac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval w a b)
    (hHac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval H a b)
    (hwd : ∀ᵐ t, 0 ≤ t → HasDerivAt w (wDot t) t)
    (hHd : ∀ᵐ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (hr : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hdiss : ∀ᵐ t, 0 ≤ t → wDot t ≤ -rate t * (1 - x t))
    (hproper : Tendsto H atTop atTop) : ∀ a, 0 ≤ a → x a = 1 := by
  have hwmono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : w b ≤ w a := by
    apply ac_endpoint_le_of_ae_hasDerivAt_nonpos hab (hwac a b ha hab)
    · filter_upwards [hwd] with t ht hmem
      exact ht (ha.trans (uIcc_of_le hab ▸ hmem).1)
    · filter_upwards [hdiss, hr] with t ht hrt hmem
      have ht0 : 0 ≤ t := ha.trans (uIcc_of_le hab ▸ hmem).1
      have hp := mul_nonneg (hrt ht0) (sub_nonneg.mpr (hx t ht0))
      nlinarith only [ht ht0, hp]
  intro a ha
  apply le_antisymm (hx a ha)
  by_contra hnot
  have hxa : x a < 1 := lt_of_not_ge hnot
  let C := max (x a) threshold
  let δ := 1 - C
  have hC : C < 1 := max_lt hxa hthreshold
  have hδ : 0 < δ := sub_pos.mpr hC
  have hmax : max (x a - threshold) 0 = C - threshold := by
    rcases le_total (x a) threshold with h | h
    · dsimp [C]
      rw [max_eq_right (sub_nonpos.mpr h), max_eq_right h, sub_self]
    · dsimp [C]
      rw [max_eq_left (sub_nonneg.mpr h), max_eq_left h]
  have hxt (t : ℝ) (hat : a ≤ t) : x t ≤ C := by
    have ht0 := ha.trans hat
    have h := hwmono a t ha hat
    rw [hw a ha, hw t ht0, hmax] at h
    have hh := le_max_left (x t - threshold) (0 : ℝ)
    linarith
  have hbound (b : ℝ) (hab : a ≤ b) :
      H b ≤ (w a + δ * H a) / δ := by
    have hac := (hwac a b ha hab).add ((hHac a b ha hab).const_mul δ)
    have he : w b + δ * H b ≤ w a + δ * H a := by
      apply ac_endpoint_le_of_ae_hasDerivAt_nonpos hab hac
      · filter_upwards [hwd, hHd] with t hwt hHt hmem
        have ht0 : 0 ≤ t := ha.trans (uIcc_of_le hab ▸ hmem).1
        exact (hwt ht0).add ((hHt ht0).const_mul δ)
      · filter_upwards [hdiss, hr] with t ht hrt hmem
        have hat : a ≤ t := (uIcc_of_le hab ▸ hmem).1
        have ht0 := ha.trans hat
        have hp := mul_nonneg (hrt ht0) (sub_nonneg.mpr (hxt t hat))
        dsimp [δ]
        nlinarith only [ht ht0, hp]
    have hwn : 0 ≤ w b := by rw [hw b (ha.trans hab)]; exact le_max_right _ _
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [he, hwn]
  obtain ⟨b, hb, hlarge⟩ := ((eventually_ge_atTop a).and
    (hproper.eventually (eventually_gt_atTop ((w a + δ * H a) / δ)))).exists
  exact (not_lt_of_ge (hbound b hb)) hlarge

end Rhone.Statistics.Identifiability.ThreeSampling
