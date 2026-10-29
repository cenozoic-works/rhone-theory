/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkedPayoff

/-! # Exposure-onset positivity with no pointwise bound or continuity of the rate -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_payoff_positive_near_marked_onset
    (A B : ℝ → Matrix ι ι ℝ) (q : ℝ → ℝ) (M : Matrix ι ι ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    (hq : LocallyIntegrable q volume) (hqn : ∀ᵐ u, 0 ≤ u → 0 ≤ q u)
    (hmark : ∀ u, A u - B u = q u • M) (w : ι → ℝ) (i : ι)
    (hzero : ∀ t, (inhomogeneousTransition B 0 t *ᵥ w) i = 0)
    (hlead : 0 < (M *ᵥ w) i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → (0 < ∫ u in (0 : ℝ)..t, q u) →
      0 < (inhomogeneousTransition A 0 t *ᵥ w) i := by
  let L := (M *ᵥ w) i / 2
  have hL : 0 < L := div_pos hlead (by norm_num)
  have hK := markedPayoffKernel_continuous A B M hA hB w i
  have hnear : ∀ᶠ p in 𝓝 ((0,0) : ℝ × ℝ), L < markedPayoffKernel A B M w i p := by
    apply hK.continuousAt.eventually
    apply eventually_gt_nhds
    rw [markedPayoffKernel_initial A B M hA hB]
    dsimp [L]
    linarith
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ, hδ, fun t ht htδ hQ => ?_⟩
  have hbound (u : ℝ) (hu : u ∈ Icc 0 t) : L ≤ markedPayoffKernel A B M w i (u,t) := by
    apply (hnear _).le
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    rw [abs_of_nonneg hu.1, abs_of_pos ht, max_eq_right hu.2]
    exact htδ
  have hiq : IntervalIntegrable q volume 0 t := locallyIntegrable_interval q hq 0 t
  have hiK : IntervalIntegrable (fun u => q u * markedPayoffKernel A B M w i (u,t)) volume 0 t :=
    hiq.mul_continuousOn (hK.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hlower : (∫ u in (0 : ℝ)..t, q u * L) ≤
      ∫ u in (0 : ℝ)..t, q u * markedPayoffKernel A B M w i (u,t) := by
    apply intervalIntegral.integral_mono_ae_restrict ht.le (hiq.mul_const L) hiK
    filter_upwards [hqn.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Icc] with u hqu hu
    exact mul_le_mul_of_nonneg_left (hbound u hu) (hqu hu.1)
  rw [intervalIntegral.integral_mul_const] at hlower
  have he := integrable_marked_payoff A B q M hA hB hmark w i t
  rw [hzero t, sub_zero] at he
  rw [he]
  exact (mul_pos hQ hL).trans_le hlower

end Rhone.Statistics.Identifiability
