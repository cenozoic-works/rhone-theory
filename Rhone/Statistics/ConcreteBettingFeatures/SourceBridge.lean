/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcreteBettingFeatures.ObserverMoments
public import Rhone.Statistics.ConcreteBettingFeatures.SourceArithmetic
public import Rhone.Statistics.ConcreteBettingFeatures.ClassSum
public import Rhone.Statistics.TwoIslandSpatial.Observer

/-! # Full-spatial source bridge and exact centred moment bounds -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.ConcreteBettingFeatures
open ConcretePatternMoments LocalizedBetting ThreeTipSites ThreeSiteSeparator
open Algebra.Identifiability MarkovChain.Identifiability Identifiability DependenceBudget
    DependentPairedTest

def sourceDurations : Measure (ℝ × ℝ) := IslandThreeTimes.durationLaw 0 1 (1 / 100)

instance sourceDurations_probability : IsProbabilityMeasure sourceDurations :=
  IslandThreeTimes.durationLaw_probability 0 (by norm_num) (by norm_num)

theorem sourceDurations_nonnegative : NonnegativeTimes sourceDurations :=
  IslandThreeTimes.durationLaw_nonnegative 0 1 (1 / 100)

def sourceLaw : Law (Panel 4 3) := observedLaw 2 sourceDurations (by norm_num)
  sourceDurations_nonnegative

def sourceContrast (x : Panel 4 3) : ℝ := contrast sourceMeans (fun i => observedFeature i x)

theorem source_spatial_observer : lawMeasure sourceLaw =
    TwoIslandSpatial.spatialSequenceLaw (uniformBlockRoots 4 3 (by norm_num))
      2 1 (1 / 100) := by
  rw [TwoIslandSpatial.spatialSequenceLaw_eq _ _ (by norm_num) (by norm_num)]
  exact observed_law_measure 2 sourceDurations (by norm_num) _

theorem source_feature_means (i : Fin 5) :
    rejection sourceLaw (observedFeature i) = sourceMeans i := by
  unfold sourceLaw
  rw [observed_feature_mean]
  have he : momentTable 2 sourceDurations = sourceValues := by
    funext j
    exact source_moment_table j
  rw [he, target_source_means]

theorem source_contrast_centered : rejection sourceLaw sourceContrast = 0 := by
  unfold sourceContrast
  rw [contrast_expectation]
  simp_rw [source_feature_means]
  exact centered_contrast sourceMeans

theorem source_contrast_class (x : Panel 4 3) :
    sourceContrast x = classContrast (rowClass (rowOf x)) := rfl

theorem source_mass_class (x : Panel 4 3) :
    sourceLaw.mass x = sourceClassMass (rowClass (rowOf x)) := by
  change mass (uniformBlockRoots 4 3 (by norm_num)) 2
    (IslandThreeTimes.durationLaw 0 1 (1 / 100)) x = _
  rw [source_full_labelled_mass]
  unfold sourceWeights tableMass coefficient
  rw [class_alignment, source_class_probabilities]

theorem source_contrast_second :
    rejection sourceLaw (fun x => sourceContrast x ^ 2) ≤ 78914008 := by
  unfold rejection
  simp_rw [source_mass_class, source_contrast_class]
  rw [category_panel_sum (fun r => sourceClassMass (rowClass r) * classContrast (rowClass r) ^ 2)]
  have he : (∑ r : Row, ConcretePatternMoments.multiplicity r.1 *
      ConcretePatternMoments.multiplicity r.2.1 * ConcretePatternMoments.multiplicity r.2.2 *
        (sourceClassMass (rowClass r) * classContrast (rowClass r) ^ 2)) =
      ∑ c : Fin 14, (sourceClassCount c : ℝ) * sourceClassMass c * classContrast c ^ 2 := by
    simp_rw [← row_multiplicity_real]
    rw [weighted_class_sum (fun c => sourceClassMass c * classContrast c ^ 2)]
    apply Finset.sum_congr rfl
    intro c _
    have hc : (∑ r : Row with rowClass r = c, (rowMultiplicity r : ℝ)) = sourceClassCount c := by
      exact_mod_cast source_class_counts c
    rw [hc]
    ring
  rw [he]
  exact source_second_moment_bound

theorem source_increment_bound (x : Panel 4 3) :
    |eta * (sourceContrast x + margin)| ≤ 1 / 100 := by
  rw [source_contrast_class]
  exact increment_bound _

end Rhone.Statistics.ConcreteBettingFeatures
