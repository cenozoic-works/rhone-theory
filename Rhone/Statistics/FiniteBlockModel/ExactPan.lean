/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FiniteBlockModel.Observer
public import Rhone.Statistics.WeakRegularSeparation.ExactComparison
public import Rhone.Statistics.Identifiability.PanThreeSampleLaw

/-! # Exact fixed-candidate bridge; uniform finite-block separation remains separate -/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Rhone.Statistics.FiniteBlockModel
open CollapsedGenealogy WeakRegularSeparation ThreeTipSites ThreeSiteSeparator
open MarkovChain.Identifiability Identifiability

theorem pan_internal_positive (r : ℝ → ℝ) :
    ∀ᵐ t ∂PanThreeSample.durationLaw r, 0 < t.2 := by
  apply (ae_map_iff PanThreeSample.measurable_toDurations.aemeasurable
    (show MeasurableSet {t : ℝ × ℝ | 0 < t.2} by measurability)).mpr
  filter_upwards [PanThreeSample.law_ordered_support r] with p hp
  exact sub_pos.mpr hp.2

theorem same_clock_all_blocks_iff_pan_duration_eq {K : ℕ} (hK : 2 ≤ K)
    {k : ℝ} (hk : 0 < k) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : NonnegativeTimes μ) (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop) :
    (∀ L : ℕ, law (uniformBlockRoots K L (by omega)) k μ =
      law (uniformBlockRoots K L (by omega)) k (PanThreeSample.durationLaw r)) ↔
        μ = PanThreeSample.durationLaw r := by
  let := PanThreeSample.durationLaw_probability r hr hn ht
  have h := all_blocks_against_positive_candidate hK hk (uniformLift μ)
    (uniformLift (PanThreeSample.durationLaw r)) (uniform_lift_nonnegative μ hμ)
    (uniform_lift_nonnegative _ (PanThreeSample.durationLaw_nonnegative r))
    (uniform_lift_internal_positive _ (pan_internal_positive r))
  simp_rw [uniform_lift_sequence_law (K := K) (by omega) _ hk.le μ hμ,
    uniform_lift_sequence_law (K := K) (by omega) _ hk.le _
      (PanThreeSample.durationLaw_nonnegative r)] at h
  exact h.trans (uniform_lift_injective μ _)

end Rhone.Statistics.FiniteBlockModel
