/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.UniformMargin

/-! # Closure of the nonpositive-score probability laws in finite TV -/

@[expose] public section

open MeasureTheory Filter
namespace Rhone.Statistics.ThreeSiteRobustness
open ThreeSiteSeparator ThreeTipSites

theorem pattern_score_tendsto_of_tv {K : ℕ} (hK : 3 ≤ K)
    (ρ : ℕ → Measure (Panel K 3)) (σ : Measure (Panel K 3))
    [∀ n, IsProbabilityMeasure (ρ n)] [IsProbabilityMeasure σ]
    (h : Tendsto (fun n => finiteTV (ρ n) σ) atTop (nhds 0)) :
    Tendsto (fun n => patternScore (ρ n)) atTop (nhds (patternScore σ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb := h.const_mul 1467240
  simp only [mul_zero] at hb
  apply squeeze_zero (fun _ => norm_nonneg _) _ hb
  intro n
  simpa only [Real.norm_eq_abs] using pattern_score_tv hK (ρ n) σ

theorem nonpositive_score_tv_closed {K : ℕ} (hK : 3 ≤ K)
    (ρ : ℕ → Measure (Panel K 3)) (σ : Measure (Panel K 3))
    [∀ n, IsProbabilityMeasure (ρ n)] [IsProbabilityMeasure σ]
    (hscore : ∀ n, patternScore (ρ n) ≤ 0)
    (h : Tendsto (fun n => finiteTV (ρ n) σ) atTop (nhds 0)) :
    patternScore σ ≤ 0 :=
  le_of_tendsto (pattern_score_tendsto_of_tv hK ρ σ h) (Filter.Eventually.of_forall hscore)

end Rhone.Statistics.ThreeSiteRobustness
