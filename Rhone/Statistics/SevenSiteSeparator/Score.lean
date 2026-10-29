/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SevenSiteSeparator.Observation
public import Rhone.Statistics.ThreeSiteSeparator.PatternScore

/-! # Seven-site score from the score certificate at twice the clock -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.SevenSiteSeparator
open ThreeSiteSeparator ThreeTipSites SingleSiteChannel

def sevenMoment {K : ℕ} (ρ : Measure (Panel K 7)) (j : Fin 5) : ℝ :=
  ∑ x, sevenFeatures j x * ρ.real {x}

def sevenScore {K : ℕ} (ρ : Measure (Panel K 7)) : ℝ :=
  score (sevenMoment ρ 0) (sevenMoment ρ 1) (sevenMoment ρ 2)
    (sevenMoment ρ 3) (sevenMoment ρ 4)

theorem sevenMoment_law {K : ℕ} (hK : 2 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) (j : Fin 5) :
    sevenMoment (law (uniformBlockRoots K 7 (by omega)) k μ) j =
      ∫ t, sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) j ∂μ := by
  have he (x : Panel K 7) :
      (law (uniformBlockRoots K 7 (by omega)) k μ).real {x} =
        mass (uniformBlockRoots K 7 (by omega)) k μ x := by
    unfold Measure.real
    rw [law_singleton, ENNReal.toReal_ofReal (mass_nonneg _ hk hμ x)]
  simp only [sevenMoment, he]
  exact seven_observed_moment hK hk hμ j

theorem double_clock_exp (k u : ℝ) : Real.exp (-(2 * k) * u) = Real.exp (-k * u) ^ 2 := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem double_clock_triple (k : ℝ) (t : ℝ × ℝ) :
    secondMomentKernel (2 * k) t =
      Real.exp (-k * t.1) * Real.exp (-k * (t.1 + t.2)) ^ 2 := by
  rw [secondMomentKernel, pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem sevenScore_law {K : ℕ} (hK : 2 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    sevenScore (law (uniformBlockRoots K 7 (by omega)) k μ) = genealogyScore (2 * k) μ := by
  unfold sevenScore genealogyScore
  simp only [sevenMoment_law hK hk hμ, double_clock_exp, double_clock_triple]
  congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with t <;>
    dsimp [sevenKernel] <;> ring

end Rhone.Statistics.SevenSiteSeparator
