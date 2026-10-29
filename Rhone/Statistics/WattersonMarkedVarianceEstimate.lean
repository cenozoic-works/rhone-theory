/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.WattersonMarkedMoments

/-! # Observed total-S estimator of the Watterson variance -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory Finset Rhone.Combinatorics MarkovChain Probability
open scoped NNReal

noncomputable def markedKingmanWattersonVarianceEstimate (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  ((tajimaA1 n : ℝ) ^ 2 * markedKingmanSegregating n x +
    (tajimaA2 n : ℝ) * markedKingmanSegregating n x ^ 2) /
      ((tajimaA1 n : ℝ) ^ 2 * ((tajimaA1 n : ℝ) ^ 2 + (tajimaA2 n : ℝ)))

theorem markedKingmanWattersonVarianceEstimate_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    (∫ x, markedKingmanWattersonVarianceEstimate n x ∂Coalescent.markedKingmanLaw n θ) =
      (θ : ℝ) / (tajimaA1 n : ℝ) +
        (θ : ℝ) ^ 2 * (tajimaA2 n : ℝ) / (tajimaA1 n : ℝ) ^ 2 := by
  have ha1 : 0 < (tajimaA1 n : ℝ) := by
    have hq : (0 : ℚ) < tajimaA1 n := zero_lt_harmonic (by omega)
    exact_mod_cast hq
  have ha2 : 0 ≤ (tajimaA2 n : ℝ) := by
    have hq : (0 : ℚ) ≤ tajimaA2 n := by
      unfold tajimaA2
      exact Finset.sum_nonneg fun i _ => div_nonneg (by norm_num) (sq_nonneg _)
    exact_mod_cast hq
  have hsum : 0 < (tajimaA1 n : ℝ) ^ 2 + (tajimaA2 n : ℝ) := by positivity
  unfold markedKingmanWattersonVarianceEstimate
  rw [integral_div, integral_add
    ((integrable_markedKingmanSegregating n θ).const_mul _)
    ((integrable_markedKingmanSegregating_sq n θ).const_mul _),
    integral_const_mul, integral_const_mul,
    markedKingmanSegregating_mean hn θ, markedKingmanSegregating_second_moment hn θ]
  field_simp [ne_of_gt ha1, ne_of_gt hsum]
  ring

end Rhone.Statistics
