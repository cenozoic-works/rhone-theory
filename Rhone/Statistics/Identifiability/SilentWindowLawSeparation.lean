/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SilentPureRecombinationHistory

/-! # A coalescence-free window endpoint for the time-varying ARG law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.SilentWindow
open SimultaneousOnset DelayedOnset

lemma witness_continuous (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) :
    Continuous (SimultaneousOnset.witness k c q r) := by
  have hU : Continuous (fun t : ℝ => inhomogeneousTransition
      (fun u => productGenerator k (c u) (q u) (r u)) 0 t) :=
    (inhomogeneousTransition_continuous
    (fun u => productGenerator k (c u) (q u) (r u))
    (productGenerator_history_continuous k c q r hc hq hr)).comp
    (continuous_const.prodMk continuous_id)
  change Continuous (fun t => SimultaneousOnset.witness k c q r t)
  simp_rw [witness_eq_product_output k c q r hc hq hr]
  simp only [Matrix.mulVec, dotProduct]
  apply continuous_finsetSum
  intro j _
  exact (((continuous_apply j).comp ((continuous_apply (0, 0)).comp hU))).mul continuous_const

lemma witness_positive_right_of_positive (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r) {b : ℝ}
    (hb : 0 < SimultaneousOnset.witness k c q r b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      0 < SimultaneousOnset.witness k c q r (b + t) := by
  have he := (SilentWindow.witness_continuous k c q r hc hq hr).continuousAt.eventually
    (eventually_gt_nhds hb)
  obtain ⟨δ, hδ, hpos⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, fun t ht htδ => hpos ?_⟩
  simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht] using htδ

theorem jointLaw_ne_pan_of_pure_recombination_silent_window (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u)
    (hpair : ∀ s, 0 ≤ s → ∀ i,
      Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0))
    {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hbefore : ∀ u ∈ Icc 0 a, r u = 0) (hQ : 0 < ∫ u in (0 : ℝ)..a, q u)
    (hsilent : ∀ u ∈ Icc a (a + T), c u = 0 ∧ q u = 0)
    (hR : 0 < ∫ u in (0 : ℝ)..T, r (a + u))
    (hresume : ∀ δ : ℝ, 0 < δ → ∃ t, 0 < t ∧ t < δ ∧ 0 < c (a + T + t))
    (P : ProperIntegrablePanModel) : timeVaryingJointLaw k c q r ≠ P.pre.jointLaw := by
  have hp := witness_positive_after_pure_recombination_window k c q r hc hq hr
    hqn hrn ha hT hbefore hQ hsilent hR
  exact jointLaw_ne_pan_of_witness_after k c q r hc hq hr hcn hqn hrn hpair
    (add_nonneg ha hT) (witness_positive_right_of_positive k c q r hc hq hr hp) hresume P

end Rhone.Statistics.Identifiability.SilentWindow
