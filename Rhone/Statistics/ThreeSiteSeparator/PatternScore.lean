/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.ObservationMoments
public import Rhone.Statistics.ThreeSiteSeparator.Score

/-! # The explicit statistic of the three-site pattern distribution -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites SingleSiteChannel

def patternMoment {K : ℕ} (ρ : Measure (Panel K 3)) (f : Panel K 3 → ℝ) : ℝ :=
  ∑ x, f x*ρ.real {x}

def patternScore {K : ℕ} (ρ : Measure (Panel K 3)) : ℝ :=
  score (patternMoment ρ aStat) (patternMoment ρ p2Stat) (patternMoment ρ p3Stat)
    (patternMoment ρ hStat) (patternMoment ρ jStat)

def genealogyScore (k : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ :=
  score (∫ t, (Real.exp (-k*t.1) + 2*Real.exp (-k*(t.1+t.2)))/3 ∂μ)
    (∫ t, (Real.exp (-k*t.1)^2 + 2*Real.exp (-k*(t.1+t.2))^2)/3 ∂μ)
    (∫ t, (Real.exp (-k*t.1)^3 + 2*Real.exp (-k*(t.1+t.2))^3)/3 ∂μ)
    (∫ t, secondMomentKernel k t*
      (Real.exp (-k*t.1)^2 + 2*Real.exp (-k*(t.1+t.2))^2)/3 ∂μ)
    (∫ t, secondMomentKernel k t*(2*Real.exp (-k*t.1)*Real.exp (-k*(t.1+t.2)) +
      Real.exp (-k*(t.1+t.2))^2)/3 ∂μ)

lemma patternMoment_law {K : ℕ} (π : Roots K 3) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} (hμ : NonnegativeTimes μ) (f : Panel K 3 → ℝ) :
    patternMoment (law π k μ) f = observationMoment π k μ f := by
  have he (x : Panel K 3) : (law π k μ).real {x} = mass π k μ x := by
    unfold Measure.real
    rw [law_singleton, ENNReal.toReal_ofReal (mass_nonneg π hk hμ x)]
  simp only [patternMoment, observationMoment, he]

theorem patternScore_law {K : ℕ} (hK : 3 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    patternScore (law (uniformBlockRoots K 3 (by omega)) k μ) = genealogyScore k μ := by
  unfold patternScore genealogyScore
  simp only [patternMoment_law _ hk hμ, observed_a_moment hK hk hμ,
    observed_p2_moment hK hk hμ, observed_p3_moment hK hk hμ,
    observed_h_moment hK hk hμ, observed_j_moment hK hk hμ]

theorem pattern_laws_ne_of_score_gap {K : ℕ} (hK : 3 ≤ K) {k ℓ : ℝ}
    (hk : 0 ≤ k) (hℓ : 0 ≤ ℓ) {μ ν : Measure (ℝ × ℝ)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hpos : 0 < genealogyScore k μ) (hneg : genealogyScore ℓ ν ≤ 0) :
    law (uniformBlockRoots K 3 (by omega)) k μ ≠
      law (uniformBlockRoots K 3 (by omega)) ℓ ν := by
  intro he
  have hs := congrArg patternScore he
  rw [patternScore_law hK hk hμ, patternScore_law hK hℓ hν] at hs
  linarith

end Rhone.Statistics.ThreeSiteSeparator
