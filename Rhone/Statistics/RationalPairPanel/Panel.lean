/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.RationalPairPanel.Grid
public import Rhone.Statistics.LinkedPairMoments.InfiniteCriterion

/-! # Finite-panel equivalence under explicit proper rational Laplace representation bounds -/

@[expose] public section

open MeasureTheory Polynomial
namespace Rhone.Statistics.RationalPairPanel
open LinkedPairMoments PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

theorem bounded_panel_eq_iff (E : Channel K H) (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (P Q R T : ℝ[X]) {d e : ℕ}
    (hP : P.natDegree < d) (hQ : Q.natDegree ≤ d)
    (hR : R.natDegree < e) (hT : T.natDegree ≤ e)
    (hQn : ∀ s : ℝ, 0 ≤ s → Q.eval s ≠ 0)
    (hTn : ∀ s : ℝ, 0 ≤ s → T.eval s ≠ 0)
    (hμrep : ∀ s : ℝ, 0 ≤ s → pairLaplace μ s = P.eval s / Q.eval s)
    (hνrep : ∀ s : ℝ, 0 ≤ s → pairLaplace ν s = R.eval s / T.eval s) :
    panelLaw E μ hk.le hμ (d + e - 1) = panelLaw E ν hk.le hν (d + e - 1) ↔ μ = ν := by
  constructor
  · intro he
    have hm := (panel_eq_iff E hE μ ν hk.le hμ hν (d + e - 1)).mp he
    have hcross : P * T = R * Q := by
      apply rational_grid_identity P Q R T hk.ne' hP hQ hR hT
        (fun i => hQn _ (mul_nonneg (by positivity) hk.le))
        (fun i => hTn _ (mul_nonneg (by positivity) hk.le))
      intro i
      have hi : 0 ≤ (i : ℝ) * k := mul_nonneg (by positivity) hk.le
      rw [← hμrep _ hi, ← hνrep _ hi]
      exact hm i (by omega)
    apply all_laplace_moments_injective μ ν hk hμ hν
    intro n
    have hn : 0 ≤ (n : ℝ) * k := mul_nonneg (Nat.cast_nonneg _) hk.le
    change pairLaplace μ _ = pairLaplace ν _
    rw [hμrep _ hn, hνrep _ hn]
    exact rational_eval_eq_of_identity hcross (hQn _ hn) (hTn _ hn)
  · rintro rfl
    rfl

theorem shared_denominator_panel_eq_iff (E : Channel K H) (hE : Informative E)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : ℝ} (hk : 0 < k) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (P R Q : ℝ[X]) {d : ℕ} (hP : P.natDegree < d) (hR : R.natDegree < d)
    (hQn : ∀ s : ℝ, 0 ≤ s → Q.eval s ≠ 0)
    (hμrep : ∀ s : ℝ, 0 ≤ s → pairLaplace μ s = P.eval s / Q.eval s)
    (hνrep : ∀ s : ℝ, 0 ≤ s → pairLaplace ν s = R.eval s / Q.eval s) :
    panelLaw E μ hk.le hμ (d - 1) = panelLaw E ν hk.le hν (d - 1) ↔ μ = ν := by
  constructor
  · intro he
    have hm := (panel_eq_iff E hE μ ν hk.le hμ hν (d - 1)).mp he
    have hpoly : P = R := by
      apply common_denominator_grid P R Q hk.ne' hP hR
        (fun i => hQn _ (mul_nonneg (by positivity) hk.le))
      intro i
      have hi : 0 ≤ (i : ℝ) * k := mul_nonneg (by positivity) hk.le
      rw [← hμrep _ hi, ← hνrep _ hi]
      exact hm i (by omega)
    apply all_laplace_moments_injective μ ν hk hμ hν
    intro n
    have hn : 0 ≤ (n : ℝ) * k := mul_nonneg (Nat.cast_nonneg _) hk.le
    change pairLaplace μ _ = pairLaplace ν _
    rw [hμrep _ hn, hνrep _ hn, hpoly]
  · rintro rfl
    rfl

end Rhone.Statistics.RationalPairPanel
