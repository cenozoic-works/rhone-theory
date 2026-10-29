/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePatternMoments.MeasureBridge
public import Rhone.Statistics.ConcreteBettingFeatures.MomentIdentity
public import Rhone.Statistics.ConcreteBettingFeatures.Calibration
public import Rhone.Statistics.DependentPairedTest.MeasureBridge

/-! # Observation-law bridge for the explicitly defined rational features -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.ConcreteBettingFeatures
open ConcretePatternMoments ThreeTipSites ThreeSiteSeparator
open DependenceBudget DependentPairedTest

def observedFeature (i : Fin 5) (x : Panel 4 3) : ℝ := feature i (rowOf x)

def observedLaw (k : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) : Law (Panel 4 3) where
  mass := mass (uniformBlockRoots 4 3 (by norm_num)) k μ
  nonneg := mass_nonneg _ hk hμ
  total := mass_sum (by norm_num) _ hk hμ

theorem observed_law_measure (k : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) :
    lawMeasure (observedLaw k μ hk hμ) = law (uniformBlockRoots 4 3 (by norm_num)) k μ := by
  apply Measure.ext_of_singleton
  intro x
  rw [law_measure_singleton, law_singleton]
  rfl

theorem observed_feature_mean (k : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (i : Fin 5) :
    rejection (observedLaw k μ hk hμ) (observedFeature i) =
      targetMoment i (momentTable k μ) := by
  change (∑ x : Panel 4 3, mass (uniformBlockRoots 4 3 (by norm_num)) k μ x *
    feature i (rowOf x)) = _
  simp_rw [mass_table hk μ hμ]
  rw [category_panel_sum (fun r => tableMass (momentTable k μ) r * feature i r)]
  convert weighted_moment_identity i (momentTable k μ) using 1
  apply Finset.sum_congr rfl
  intro r _
  unfold tableMass
  ring

theorem observed_feature_bounds (i : Fin 5) (x : Panel 4 3) :
    -1 / 3 ≤ observedFeature i x ∧ observedFeature i x ≤ 1 := feature_bounds i (rowOf x)

theorem target_source_means (i : Fin 5) : targetMoment i sourceValues = sourceMeans i := by
  fin_cases i
  all_goals simp only [targetMoment, Fin.sum_univ_succ, Fin.sum_univ_zero]
  · change (((((0 : ℤ) : ℝ) * ((1 : ℝ) / 1)) + ((((2 : ℤ) : ℝ) * ((45603 : ℝ) / 230885)) +
      ((((0 : ℤ) : ℝ) * ((50351 : ℝ) / 592283)) + ((((0 : ℤ) : ℝ) * ((105501 : ℝ) /
      2229215)) + ((((0 : ℤ) : ℝ) * ((20251 : ℝ) / 122915)) + ((((0 : ℤ) : ℝ) * ((9537 : ℝ)
      / 128143)) + ((((0 : ℤ) : ℝ) * ((120551 : ℝ) / 2829307)) + ((((1 : ℤ) : ℝ) * ((453 :
      ℝ) / 757)) + ((((0 : ℤ) : ℝ) * ((25301 : ℝ) / 179035)) + ((((0 : ℤ) : ℝ) * ((70451 :
      ℝ) / 1064495)) + ((((0 : ℤ) : ℝ) * ((406803 : ℝ) / 10499497)) + ((((0 : ℤ) : ℝ) *
      ((91053 : ℝ) / 735965)) + ((((0 : ℤ) : ℝ) * ((80501 : ℝ) / 1351051)) + ((((0 : ℤ) : ℝ)
      * ((16739 : ℝ) / 471199)) + ((((0 : ℤ) : ℝ) * ((251 : ℝ) / 587)) + ((((0 : ℤ) : ℝ) *
      ((35401 : ℝ) / 321775)) + ((((0 : ℤ) : ℝ) * ((271653 : ℝ) / 5013721)) + ((((0 : ℤ) :
      ℝ) * ((40451 : ℝ) / 408395)) + ((((0 : ℤ) : ℝ) * ((351 : ℝ) / 1055)) +
      0))))))))))))))))))) / 3) = ((101 : ℝ) / 305)
    norm_num
  · change (((((0 : ℤ) : ℝ) * ((1 : ℝ) / 1)) + ((((0 : ℤ) : ℝ) * ((45603 : ℝ) / 230885)) +
      ((((2 : ℤ) : ℝ) * ((50351 : ℝ) / 592283)) + ((((0 : ℤ) : ℝ) * ((105501 : ℝ) /
      2229215)) + ((((0 : ℤ) : ℝ) * ((20251 : ℝ) / 122915)) + ((((0 : ℤ) : ℝ) * ((9537 : ℝ)
      / 128143)) + ((((0 : ℤ) : ℝ) * ((120551 : ℝ) / 2829307)) + ((((0 : ℤ) : ℝ) * ((453 :
      ℝ) / 757)) + ((((0 : ℤ) : ℝ) * ((25301 : ℝ) / 179035)) + ((((0 : ℤ) : ℝ) * ((70451 :
      ℝ) / 1064495)) + ((((0 : ℤ) : ℝ) * ((406803 : ℝ) / 10499497)) + ((((0 : ℤ) : ℝ) *
      ((91053 : ℝ) / 735965)) + ((((0 : ℤ) : ℝ) * ((80501 : ℝ) / 1351051)) + ((((0 : ℤ) : ℝ)
      * ((16739 : ℝ) / 471199)) + ((((1 : ℤ) : ℝ) * ((251 : ℝ) / 587)) + ((((0 : ℤ) : ℝ) *
      ((35401 : ℝ) / 321775)) + ((((0 : ℤ) : ℝ) * ((271653 : ℝ) / 5013721)) + ((((0 : ℤ) :
      ℝ) * ((40451 : ℝ) / 408395)) + ((((0 : ℤ) : ℝ) * ((351 : ℝ) / 1055)) +
      0))))))))))))))))))) / 3) = ((201 : ℝ) / 1009)
    norm_num
  · change (((((0 : ℤ) : ℝ) * ((1 : ℝ) / 1)) + ((((0 : ℤ) : ℝ) * ((45603 : ℝ) / 230885)) +
      ((((0 : ℤ) : ℝ) * ((50351 : ℝ) / 592283)) + ((((2 : ℤ) : ℝ) * ((105501 : ℝ) /
      2229215)) + ((((0 : ℤ) : ℝ) * ((20251 : ℝ) / 122915)) + ((((0 : ℤ) : ℝ) * ((9537 : ℝ)
      / 128143)) + ((((0 : ℤ) : ℝ) * ((120551 : ℝ) / 2829307)) + ((((0 : ℤ) : ℝ) * ((453 :
      ℝ) / 757)) + ((((0 : ℤ) : ℝ) * ((25301 : ℝ) / 179035)) + ((((0 : ℤ) : ℝ) * ((70451 :
      ℝ) / 1064495)) + ((((0 : ℤ) : ℝ) * ((406803 : ℝ) / 10499497)) + ((((0 : ℤ) : ℝ) *
      ((91053 : ℝ) / 735965)) + ((((0 : ℤ) : ℝ) * ((80501 : ℝ) / 1351051)) + ((((0 : ℤ) : ℝ)
      * ((16739 : ℝ) / 471199)) + ((((0 : ℤ) : ℝ) * ((251 : ℝ) / 587)) + ((((0 : ℤ) : ℝ) *
      ((35401 : ℝ) / 321775)) + ((((0 : ℤ) : ℝ) * ((271653 : ℝ) / 5013721)) + ((((0 : ℤ) :
      ℝ) * ((40451 : ℝ) / 408395)) + ((((1 : ℤ) : ℝ) * ((351 : ℝ) / 1055)) +
      0))))))))))))))))))) / 3) = ((301 : ℝ) / 2113)
    norm_num
  · change (((((0 : ℤ) : ℝ) * ((1 : ℝ) / 1)) + ((((0 : ℤ) : ℝ) * ((45603 : ℝ) / 230885)) +
      ((((0 : ℤ) : ℝ) * ((50351 : ℝ) / 592283)) + ((((0 : ℤ) : ℝ) * ((105501 : ℝ) /
      2229215)) + ((((0 : ℤ) : ℝ) * ((20251 : ℝ) / 122915)) + ((((0 : ℤ) : ℝ) * ((9537 : ℝ)
      / 128143)) + ((((2 : ℤ) : ℝ) * ((120551 : ℝ) / 2829307)) + ((((0 : ℤ) : ℝ) * ((453 :
      ℝ) / 757)) + ((((0 : ℤ) : ℝ) * ((25301 : ℝ) / 179035)) + ((((0 : ℤ) : ℝ) * ((70451 :
      ℝ) / 1064495)) + ((((0 : ℤ) : ℝ) * ((406803 : ℝ) / 10499497)) + ((((0 : ℤ) : ℝ) *
      ((91053 : ℝ) / 735965)) + ((((0 : ℤ) : ℝ) * ((80501 : ℝ) / 1351051)) + ((((0 : ℤ) : ℝ)
      * ((16739 : ℝ) / 471199)) + ((((0 : ℤ) : ℝ) * ((251 : ℝ) / 587)) + ((((0 : ℤ) : ℝ) *
      ((35401 : ℝ) / 321775)) + ((((0 : ℤ) : ℝ) * ((271653 : ℝ) / 5013721)) + ((((1 : ℤ) :
      ℝ) * ((40451 : ℝ) / 408395)) + ((((0 : ℤ) : ℝ) * ((351 : ℝ) / 1055)) +
      0))))))))))))))))))) / 3) = ((159009073 : ℝ) / 2588815905)
    norm_num
  · change (((((0 : ℤ) : ℝ) * ((1 : ℝ) / 1)) + ((((0 : ℤ) : ℝ) * ((45603 : ℝ) / 230885)) +
      ((((0 : ℤ) : ℝ) * ((50351 : ℝ) / 592283)) + ((((0 : ℤ) : ℝ) * ((105501 : ℝ) /
      2229215)) + ((((0 : ℤ) : ℝ) * ((20251 : ℝ) / 122915)) + ((((0 : ℤ) : ℝ) * ((9537 : ℝ)
      / 128143)) + ((((1 : ℤ) : ℝ) * ((120551 : ℝ) / 2829307)) + ((((0 : ℤ) : ℝ) * ((453 :
      ℝ) / 757)) + ((((0 : ℤ) : ℝ) * ((25301 : ℝ) / 179035)) + ((((0 : ℤ) : ℝ) * ((70451 :
      ℝ) / 1064495)) + ((((0 : ℤ) : ℝ) * ((406803 : ℝ) / 10499497)) + ((((0 : ℤ) : ℝ) *
      ((91053 : ℝ) / 735965)) + ((((2 : ℤ) : ℝ) * ((80501 : ℝ) / 1351051)) + ((((0 : ℤ) : ℝ)
      * ((16739 : ℝ) / 471199)) + ((((0 : ℤ) : ℝ) * ((251 : ℝ) / 587)) + ((((0 : ℤ) : ℝ) *
      ((35401 : ℝ) / 321775)) + ((((0 : ℤ) : ℝ) * ((271653 : ℝ) / 5013721)) + ((((0 : ℤ) :
      ℝ) * ((40451 : ℝ) / 408395)) + ((((0 : ℤ) : ℝ) * ((351 : ℝ) / 1055)) +
      0))))))))))))))))))) / 3) = ((153944395 : ℝ) / 2854770763)
    norm_num

end Rhone.Statistics.ConcreteBettingFeatures
