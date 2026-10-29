/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePanGrid.ModelTable

/-! # Fixed proper-pan comparator obstruction on full labelled iid observations -/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Rhone.Statistics.ConcretePanGrid
open ThreeTipSites ThreeSiteSeparator Algebra.Identifiability MarkovChain.Identifiability
    Identifiability
open DependenceBudget DependentPairedTest ConcreteBettingFeatures
open FinitePanelSampling

theorem iid_integral {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (P : Law X) (N : ℕ) (φ : (Fin N → X) → ℝ) :
    (∫ x, φ x ∂iidLaw (lawMeasure P) N) = rejection (iid P N) φ := by
  rw [integral_fintype (by fun_prop)]
  simp only [iid_measure_real_singleton, smul_eq_mul, rejection]

theorem exists_pan_full_sequence_obstruction :
    ∃ r : ℝ → ℝ, LocallyIntegrable r volume ∧ (∀ t, 0 ≤ r t) ∧
      Tendsto (integratedClock r) atTop atTop ∧
      ∀ N : ℕ, N ≤ 38318671 → ∀ φ : (Fin N → Panel 4 3) → ℝ,
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) →
        (∫ x, φ x ∂iidLaw
          (law (uniformBlockRoots 4 3 (by norm_num)) 2 (PanThreeSample.durationLaw r)) N) ≤
            (1 : ℝ) / 20 →
        (∫ x, φ x ∂iidLaw
          (TwoIslandSpatial.spatialSequenceLaw (uniformBlockRoots 4 3 (by norm_num))
            2 1 (1 / 100)) N) < (4 : ℝ) / 5 := by
  obtain ⟨r, hr, hn, ht, he⟩ := exists_pan_candidate_law
  refine ⟨r, hr, hn, ht, ?_⟩
  intro N hN φ hφ hsize
  rw [he, iid_integral] at hsize
  rw [← source_spatial_observer, iid_integral]
  exact source_finite_candidate_obstruction hN φ hφ hsize

end Rhone.Statistics.ConcretePanGrid
