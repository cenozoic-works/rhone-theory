/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.SingleSite.IslandContinuity
public import Rhone.Statistics.Identifiability.FiniteSequenceCounterexample
public import Rhone.Statistics.SingleSite.LocalOpen

/-! # Stationary-site moments at unit pan and bounded kernel estimates -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.SingleSite
open Algebra.Identifiability MarkovChain.Identifiability Identifiability SingleSiteChannel

lemma first_kernel_bounds {k : ℝ} (hk : 0 ≤ k) (p : ℝ × ℝ)
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) : 0 ≤ firstMomentKernel k p ∧ firstMomentKernel k p ≤ 1 := by
  have h1 : Real.exp (-k * p.1) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk) hp.1)
  have h2 : Real.exp (-k * (p.1 + p.2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk)
      (add_nonneg hp.1 hp.2))
  unfold firstMomentKernel
  constructor
  · positivity
  · linarith

lemma second_kernel_bounds {k : ℝ} (hk : 0 ≤ k) (p : ℝ × ℝ)
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) : 0 ≤ secondMomentKernel k p ∧ secondMomentKernel k p ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith : -(k / 2) ≤ 0) (by linarith [hp.1, hp.2])

lemma laplace_integrable (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : ThreeTipSites.NonnegativeTimes μ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Integrable (fun p => Real.exp (-s * p.1 - t * p.2)) μ := by
  convert! exp_integrable hμ hs ht using 1
  ext p
  congr 1
  ring

lemma unit_pan_first_moment {k : ℝ} (hk : 0 ≤ k) :
    firstMoment k (PanThreeSample.durationLaw (fun _ => 1)) = pairMoment k 1 := by
  let μ := PanThreeSample.durationLaw (fun _ => (1 : ℝ))
  let : IsProbabilityMeasure (PanThreeSample.law (fun _ => (1 : ℝ))) :=
    ThreeNoMigration.pan_const_probability (by norm_num)
  let : IsProbabilityMeasure μ :=
    by change IsProbabilityMeasure (Measure.map _ _); infer_instance
  have hμ := PanThreeSample.durationLaw_nonnegative (fun _ => (1 : ℝ))
  have hi1 := laplace_integrable μ hμ hk (le_refl (0 : ℝ))
  have hi2 := laplace_integrable μ hμ hk hk
  have he : firstMomentKernel k = fun p : ℝ × ℝ =>
      (Real.exp (-k * p.1 - 0 * p.2) + 2 * Real.exp (-k * p.1 - k * p.2)) / 3 := by
    funext p
    have hh : -k * (p.1 + p.2) = -k * p.1 - k * p.2 := by ring
    simp [firstMomentKernel, hh]
  rw [firstMoment, he, integral_div, integral_add hi1 (hi2.const_mul 2), integral_const_mul,
    FiniteSequenceCounterexample.unit_pan_duration_laplace k 0 hk (le_refl 0),
    FiniteSequenceCounterexample.unit_pan_duration_laplace k k hk hk]
  unfold pairMoment
  have h1 : 1 + k ≠ 0 := by positivity
  have h3 : 3 + k ≠ 0 := by positivity
  field_simp
  ring

lemma unit_pan_second_moment {k : ℝ} (hk : 0 ≤ k) :
    secondMoment k (PanThreeSample.durationLaw (fun _ => 1)) = tripleMoment k 1 := by
  have he : secondMomentKernel k = fun p : ℝ × ℝ =>
      Real.exp (-(3 * k / 2) * p.1 - k * p.2) := by
    funext p
    unfold secondMomentKernel
    congr 1
    ring
  rw [secondMoment, he,
    FiniteSequenceCounterexample.unit_pan_duration_laplace _ _ (by positivity) hk]
  unfold tripleMoment
  have h1 : 1 + k ≠ 0 := by positivity
  have h2 : 2 + k ≠ 0 := by positivity
  have h3 : 3 + 3 * k / 2 ≠ 0 := by positivity
  field_simp

end Rhone.Statistics.SingleSite
