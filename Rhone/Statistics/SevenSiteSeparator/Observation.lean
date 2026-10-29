/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SevenSiteSeparator.Words
public import Rhone.Statistics.ThreeSiteSeparator.ObservationMoments

/-! # Seven-site observation bridge, with one shared genealogy -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.SevenSiteSeparator
open ThreeSiteSeparator ThreeTipSites SingleSiteChannel

theorem seven_conditional_mean {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ)
    (j : Fin 5) :
    (∑ x, sevenFeatures j x * conditional (uniformBlockRoots K 7 (by omega)) k t x) =
      sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) j := by
  have he (x : Panel K 7) :
      sevenFeatures j x * conditional (uniformBlockRoots K 7 (by omega)) k t x =
        (1 / 3 : ℝ) * ∑ q : Fin 3,
          sevenFeatures j x * fixedTopology (uniformBlockRoots K 7 (by omega)) k t q x := by
    unfold conditional
    rw [← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_comm]
  change (1 / 3 : ℝ) * ∑ q : Fin 3,
    fixedSevenMean (uniformBlockRoots K 7 (by omega)) k t q (sevenFeatures j) = _
  simp_rw [seven_fixed_mean hK]
  norm_num
  ring

theorem seven_observed_moment {K : ℕ} (hK : 2 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) (j : Fin 5) :
    observationMoment (uniformBlockRoots K 7 (by omega)) k μ (sevenFeatures j) =
      ∫ t, sevenKernel (Real.exp (-k * t.1)) (Real.exp (-k * (t.1 + t.2))) j ∂μ := by
  rw [observationMoment_eq_integral (by omega) _ hk hμ]
  simp_rw [seven_conditional_mean hK]

end Rhone.Statistics.SevenSiteSeparator
