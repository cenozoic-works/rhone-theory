/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.EmpiricalMoments

/-! # Five-feature score tail; no within-block independence premise -/

@[expose] public section

open MeasureTheory Set
namespace Rhone.Statistics.ThreeSiteRobustness
open ThreeSiteSeparator ThreeTipSites
open Identifiability.FinitePanelSampling

theorem iid_score_error_bound {K N : ℕ} (hK : 3 ≤ K)
    (ρ : Measure (Panel K 3)) [IsProbabilityMeasure ρ] (hN : 0 < N)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (iidLaw ρ N).real {x | 733620 * ε < |empiricalScore x - patternScore ρ|} ≤
      10 * Real.exp (-(N : ℝ) * ε ^ 2 / 2) := by
  have ht := iid_finite_scores_abs_ge ρ panelFeatures (fun _ => by fun_prop)
    (panelFeatures_bounded hK) hN hε
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, mul_one] at ht
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) ht
  intro x hx
  change ∃ i, ε ≤ |sampleMean (panelFeatures i) x - ∫ y, panelFeatures i y ∂ρ|
  by_contra hn
  push Not at hn
  have hb := score_lipschitz (empirical_feature_bound hK hN x)
    (integral_panelFeatures_bound hK ρ) (fun i => le_of_lt (hn i))
  rw [scoreVector_integral_panelFeatures] at hb
  exact (not_lt_of_ge hb) hx

end Rhone.Statistics.ThreeSiteRobustness
