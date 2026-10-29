/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcreteBettingFeatures.ObserverMoments
public import Rhone.Statistics.ThreeSiteSeparator.PanScoreBound

/-! # Null-score identification for every proper locally integrable pan history -/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Rhone.Statistics.ConcreteBettingFeatures
open ConcretePatternMoments ThreeTipSites ThreeSiteSeparator
open ThreeSiteRobustness Algebra.Identifiability MarkovChain.Identifiability Identifiability
    DependenceBudget
open SingleSiteChannel

def kernelFeature (i : Fin 5) (k : ℝ) (t : ℝ × ℝ) : ℝ :=
  ![(Real.exp (-k * t.1) + 2 * Real.exp (-k * (t.1 + t.2))) / 3,
    (Real.exp (-k * t.1) ^ 2 + 2 * Real.exp (-k * (t.1 + t.2)) ^ 2) / 3,
    (Real.exp (-k * t.1) ^ 3 + 2 * Real.exp (-k * (t.1 + t.2)) ^ 3) / 3,
    secondMomentKernel k t *
      (Real.exp (-k * t.1) ^ 2 + 2 * Real.exp (-k * (t.1 + t.2)) ^ 2) / 3,
    secondMomentKernel k t * (2 * Real.exp (-k * t.1) * Real.exp (-k * (t.1 + t.2)) +
      Real.exp (-k * (t.1 + t.2)) ^ 2) / 3] i

theorem kernel_feature_identity (i : Fin 5) (k : ℝ) (t : ℝ × ℝ) :
    (∑ j : Fin 19, (targetNumerator i j : ℝ) * scaledKernel k (exponents j).1
      (exponents j).2 t) / 3 = kernelFeature i k t := by
  simp_rw [← monomial_scaled_kernel]
  obtain ⟨h1, h2, h3⟩ := decay_identities k t
  fin_cases i
  all_goals simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  · change (((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 0)) + ((((2 : ℤ) : ℝ) *
      (firstDecay k t ^ 0 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 *
      lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 6)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 1 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 1 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 1 *
      lastDecay k t ^ 6)) + ((((1 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 0)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 2 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 3 * lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 *
      lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 5 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 6 *
      lastDecay k t ^ 0)) + 0))))))))))))))))))) / 3) = ((Real.exp (-k * t.1) + 2 * Real.exp
      (-k * (t.1 + t.2))) / 3)
    simp_rw [← h1, ← h2]
    ring
  · change (((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 0 * lastDecay k t ^ 2)) + ((((2 : ℤ) : ℝ) * (firstDecay k t ^ 0 *
      lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 6)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 1 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 1 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 1 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 0)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 2 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 3 * lastDecay k t ^ 6)) + ((((1 : ℤ) : ℝ) * (firstDecay k t ^ 4 *
      lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 5 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 6 *
      lastDecay k t ^ 0)) + 0))))))))))))))))))) / 3) = ((Real.exp (-k * t.1) ^ 2 + 2 *
      Real.exp (-k * (t.1 + t.2)) ^ 2) / 3)
    simp_rw [← h1, ← h2]
    ring
  · change (((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 0 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 *
      lastDecay k t ^ 4)) + ((((2 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 6)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 1 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 1 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 1 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 0)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 2 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 3 * lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 *
      lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 5 * lastDecay k t ^ 2)) + ((((1 : ℤ) : ℝ) * (firstDecay k t ^ 6 *
      lastDecay k t ^ 0)) + 0))))))))))))))))))) / 3) = ((Real.exp (-k * t.1) ^ 3 + 2 *
      Real.exp (-k * (t.1 + t.2)) ^ 3) / 3)
    simp_rw [← h1, ← h2]
    ring
  · change (((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 0 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 *
      lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 6)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 1 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 1 * lastDecay k t ^ 4)) + ((((2 : ℤ) : ℝ) * (firstDecay k t ^ 1 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 0)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 2 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 3 * lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 *
      lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 4)) + ((((1 : ℤ) : ℝ) *
      (firstDecay k t ^ 5 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 6 *
      lastDecay k t ^ 0)) + 0))))))))))))))))))) / 3) = (secondMomentKernel k t * (Real.exp
      (-k * t.1) ^ 2 + 2 * Real.exp (-k * (t.1 + t.2)) ^ 2) / 3)
    simp_rw [← h1, ← h2, ← h3]
    ring
  · change (((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 0 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 *
      lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 0 * lastDecay k t ^ 6)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 1 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 1 * lastDecay k t ^ 4)) + ((((1 : ℤ) : ℝ) * (firstDecay k t ^ 1 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 0)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 2 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 2 *
      lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 2)) +
      ((((2 : ℤ) : ℝ) * (firstDecay k t ^ 3 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 3 * lastDecay k t ^ 6)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 *
      lastDecay k t ^ 0)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 2)) +
      ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 4 * lastDecay k t ^ 4)) + ((((0 : ℤ) : ℝ) *
      (firstDecay k t ^ 5 * lastDecay k t ^ 2)) + ((((0 : ℤ) : ℝ) * (firstDecay k t ^ 6 *
      lastDecay k t ^ 0)) + 0))))))))))))))))))) / 3) = (secondMomentKernel k t * (2 *
      Real.exp (-k * t.1) * Real.exp (-k * (t.1 + t.2)) + Real.exp (-k * (t.1 + t.2)) ^ 2) /
      3)
    simp_rw [← h1, ← h2, ← h3]
    ring

theorem target_moment_integral (i : Fin 5) {k : ℝ} (hk : 0 ≤ k)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    targetMoment i (momentTable k μ) = ∫ t, kernelFeature i k t ∂μ := by
  simp_rw [← kernel_feature_identity i k]
  rw [integral_div, integral_finsetSum _ (fun j _ =>
    (scaled_kernel_integrable hk _ _ μ hμ).const_mul (targetNumerator i j : ℝ))]
  simp only [integral_const_mul, targetMoment, momentTable]

theorem observed_score (k : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) :
    scoreVector (fun i => rejection (observedLaw k μ hk hμ) (observedFeature i)) =
      genealogyScore k μ := by
  simp_rw [observed_feature_mean, target_moment_integral _ hk μ hμ]
  rfl

theorem pan_nonnegative (r : ℝ → ℝ) : NonnegativeTimes (PanThreeSample.durationLaw r) :=
  PanThreeSample.durationLaw_nonnegative r

theorem pan_score_nonpositive (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {k : ℝ} (hk : 0 < k) :
    letI := PanThreeSample.durationLaw_probability r hr hn ht
    scoreVector (fun i => rejection
      (observedLaw k (PanThreeSample.durationLaw r) hk.le
        (pan_nonnegative r)) (observedFeature i)) ≤ 0 := by
  let := PanThreeSample.durationLaw_probability r hr hn ht
  rw [observed_score]
  exact pan_genealogy_score_nonpos r hr hn ht hk

end Rhone.Statistics.ConcreteBettingFeatures
