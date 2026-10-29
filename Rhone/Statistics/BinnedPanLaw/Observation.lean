/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.PanRealization
public import Rhone.Statistics.ThreeSiteSeparator.PanSortedMoments
public import Rhone.Statistics.ConcretePatternMoments.MeasureBridge

/-! # Analytic bridge from the realized histogram to full labelled observations -/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Rhone.Statistics.BinnedPanLaw
open Algebra.Identifiability MarkovChain.Identifiability Identifiability ThreeSiteSeparator
    ConcretePatternMoments ThreeTipSites

def histogramMoments {n : ℕ} (w : Fin n → ℝ) (j : Fin 19) : ℝ :=
  ∫ z, z.1 ^ (exponents j).1 * z.2 ^ (exponents j).2 ∂sortedPairLaw (histogram w)

theorem realized_histogram_moments {n : ℕ} (w : Fin n → ℝ) (r : ℝ → ℝ)
    (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop)
    (he : (panPairLaw r).map (fun t : ℝ => Real.exp (-t)) = histogram w) :
    momentTable 2 (PanThreeSample.durationLaw r) = histogramMoments w := by
  have hc : panClockLaw 1 r = histogram w := by
    rw [panClockLaw_exp (by norm_num : (0 : ℝ) ≤ 1)]
    simpa only [neg_one_mul] using he
  funext j
  have hk : scaledKernel 2 (exponents j).1 (exponents j).2 =
      scaledDurationKernel 1 (exponents j).1 (exponents j).2 := by
    funext t
    unfold scaledKernel scaledDurationKernel
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  unfold momentTable histogramMoments
  rw [hk, pan_duration_sorted_moment r hr hn ht (by norm_num), hc]

theorem exists_pan_full_pattern_histogram {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1) :
    ∃ r : ℝ → ℝ, LocallyIntegrable r volume ∧ (∀ t, 0 ≤ r t) ∧
      Tendsto (integratedClock r) atTop atTop ∧
      ∀ x : Panel 4 3,
        mass (uniformBlockRoots 4 3 (by norm_num)) 2 (PanThreeSample.durationLaw r) x =
          tableMass (histogramMoments w) (rowOf x) := by
  obtain ⟨r, hr, hnn, ht, he⟩ := exists_pan_histogram hn w hw hs
  refine ⟨r, hr, hnn, ht, ?_⟩
  let := PanThreeSample.durationLaw_probability r hr hnn ht
  intro x
  rw [mass_table (by norm_num) _ (PanThreeSample.durationLaw_nonnegative r),
    realized_histogram_moments w r hr hnn ht he]

end Rhone.Statistics.BinnedPanLaw
