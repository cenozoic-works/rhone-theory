/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ErlangPhase.DurationProduct
public import Rhone.Statistics.PairObservationChannel.LaplaceKernel

/-! # Exact continuous pair-time measures for a linked-site example -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Rhone.Statistics.LinkedPairTimes
open FoldedCounts PairObservationChannel

def simpleTime : Measure ℝ := exponential 1

def mixtureTime : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • exponential (1 / 2) + (1 / 2 : ℝ≥0∞) • exponential 2

instance simple_probability : IsProbabilityMeasure simpleTime :=
  exponential_probability (by norm_num)

instance mixture_probability : IsProbabilityMeasure mixtureTime := by
  let : IsProbabilityMeasure (exponential (1 / 2)) := exponential_probability (by norm_num)
  let : IsProbabilityMeasure (exponential 2) := exponential_probability (by norm_num)
  constructor
  norm_num [mixtureTime, ENNReal.inv_two_add_inv_two]

theorem exponential_positive_support (a : ℝ) : ∀ᵐ t ∂exponential a, 0 < t := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact ae_restrict_mem measurableSet_Ioi

theorem simple_nonnegative : ∀ᵐ t ∂simpleTime, 0 ≤ t :=
  (exponential_positive_support 1).mono fun _ h => h.le

theorem mixture_nonnegative : ∀ᵐ t ∂mixtureTime, 0 ≤ t := by
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure
      ((exponential_positive_support (1 / 2)).mono (fun _ h => h.le)) _
  · exact Measure.ae_smul_measure
      ((exponential_positive_support 2).mono (fun _ h => h.le)) _

theorem simple_laplace {k : ℝ} (hk : 0 ≤ k) : pairLaplace simpleTime k = 1 / (1 + k) :=
  ErlangPhase.exponential_laplace 1 k (by norm_num) hk

theorem mixture_laplace {k : ℝ} (hk : 0 ≤ k) :
    pairLaplace mixtureTime k = (1 / 2 : ℝ) * ((1 / 2) / (1 / 2 + k)) +
      (1 / 2 : ℝ) * (2 / (2 + k)) := by
  let : IsProbabilityMeasure (exponential (1 / 2)) := exponential_probability (by norm_num)
  let : IsProbabilityMeasure (exponential 2) := exponential_probability (by norm_num)
  have h1 := exp_integrable (exponential (1 / 2)) hk
    ((exponential_positive_support (1 / 2)).mono fun _ h => h.le)
  have h2 := exp_integrable (exponential 2) hk
    ((exponential_positive_support 2).mono fun _ h => h.le)
  unfold pairLaplace mixtureTime
  rw [integral_add_measure (h1.smul_measure (by norm_num)) (h2.smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure]
  rw [ErlangPhase.exponential_laplace _ _ (by norm_num) hk,
    ErlangPhase.exponential_laplace _ _ (by norm_num) hk]
  norm_num

theorem first_laplace_tie : pairLaplace simpleTime 1 = pairLaplace mixtureTime 1 := by
  rw [simple_laplace (by norm_num), mixture_laplace (by norm_num)]
  norm_num

theorem second_laplace_gap :
    pairLaplace mixtureTime 2 - pairLaplace simpleTime 2 = (1 : ℝ) / 60 := by
  rw [simple_laplace (by norm_num), mixture_laplace (by norm_num)]
  norm_num

end Rhone.Statistics.LinkedPairTimes
