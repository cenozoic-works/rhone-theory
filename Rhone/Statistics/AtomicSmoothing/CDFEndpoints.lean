/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.MixtureLaw

/-! # Exact zero/one tails of the concrete compactly supported mixture CDF -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.AtomicSmoothing

lemma componentCDF_below {a τ x : ℝ} (hτ : 0 < τ) (hl : 0 ≤ a - τ) (hx : x ≤ 0) :
    componentCDF a τ x = 0 := by
  have he : (x - (a - τ)) / (2 * τ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith) (by positivity)
  unfold componentCDF
  rw [clip_zero he, clip_zero hx]
  ring

lemma componentCDF_above {a τ x : ℝ} (hτ : 0 < τ) (hu : a + τ ≤ 1) (hx : 1 ≤ x) :
    componentCDF a τ x = 1 := by
  have he : 1 ≤ (x - (a - τ)) / (2 * τ) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * τ)).mpr (by linarith)
  unfold componentCDF
  rw [clip_one he, clip_one hx]
  ring

lemma mixtureCDF_below {α : Type*} [Fintype α] (loc w : α → ℝ) {τ x : ℝ}
    (hτ : 0 < τ) (hl : ∀ a, 0 ≤ loc a - τ) (hx : x ≤ 0) : mixtureCDF loc w τ x = 0 := by
  simp [mixtureCDF, componentCDF_below hτ (hl _) hx]

lemma mixtureCDF_above {α : Type*} [Fintype α] (loc w : α → ℝ) {τ x : ℝ}
    (hτ : 0 < τ) (hu : ∀ a, loc a + τ ≤ 1) (hs : ∑ a, w a = 1) (hx : 1 ≤ x) :
    mixtureCDF loc w τ x = 1 := by
  simp [mixtureCDF, componentCDF_above hτ (hu _) hx, hs]

end Rhone.Statistics.AtomicSmoothing
