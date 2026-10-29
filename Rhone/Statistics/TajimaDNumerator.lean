/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.WattersonMarkedMoments
public import Rhone.Statistics.TajimaVariance
public import Rhone.Statistics.TajimaMoments

/-!
# The numerator of Tajima's D and the mean of its variance estimate

Source: tajima1989, p. 588, eq. (28)–(30); watterson1975, p. 258, eq. (1.4a)–(1.5a); durrett2008,
Thm 1.22. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Rhone.Combinatorics MarkovChain Probability
open scoped NNReal

theorem tajimaA1_real_pos {n : ℕ} (hn : 2 ≤ n) : 0 < (tajimaA1 n : ℝ) := by
  have hq : (0 : ℚ) < tajimaA1 n := zero_lt_harmonic (by omega)
  exact_mod_cast hq

theorem tajimaA2_real_nonneg (n : ℕ) : 0 ≤ (tajimaA2 n : ℝ) := by
  have hq : (0 : ℚ) ≤ tajimaA2 n := by
    unfold tajimaA2
    exact Finset.sum_nonneg fun i _ => div_nonneg (by norm_num) (sq_nonneg _)
  exact_mod_cast hq

theorem integrable_markedKingmanWatterson (n : ℕ) (θ : ℝ≥0) :
    Integrable (markedKingmanWatterson n) (Coalescent.markedKingmanLaw n θ) := by
  unfold markedKingmanWatterson
  exact (integrable_markedKingmanSegregating n θ).div_const _

theorem measurable_markedKingmanTajimaNumerator (n : ℕ) :
    Measurable (markedKingmanTajimaNumerator n) := by
  unfold markedKingmanTajimaNumerator markedKingmanWatterson
  exact (Coalescent.measurable_markedKingmanPi n).sub
    ((measurable_markedKingmanSegregating n).div_const _)

theorem integrable_markedKingmanTajimaNumerator {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    Integrable (markedKingmanTajimaNumerator n) (Coalescent.markedKingmanLaw n θ) := by
  unfold markedKingmanTajimaNumerator
  exact (Coalescent.integrable_markedKingmanPi hn θ).sub (integrable_markedKingmanWatterson n θ)

/-- Source: tajima1989, p. 588, eq. (28)–(29). -/
theorem markedKingmanTajimaNumerator_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanTajimaNumerator n x ∂Coalescent.markedKingmanLaw n θ = 0 := by
  unfold markedKingmanTajimaNumerator
  rw [integral_sub (Coalescent.integrable_markedKingmanPi hn θ)
      (integrable_markedKingmanWatterson n θ),
    markedKingmanPi_mean hn θ, markedKingmanWatterson_mean hn θ, sub_self]

/--
Source: tajima1989, p. 588, eq. (34)–(35); watterson1975, p. 258, eq. (1.4a)–(1.5a); fu_li1993, p.
696, eq. (20)–(21). -/
theorem markedKingmanTajimaVarianceEstimate_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanTajimaVarianceEstimate n x ∂Coalescent.markedKingmanLaw n θ =
      (tajimaC1 n : ℝ) * θ + (tajimaC2 n : ℝ) * (θ : ℝ) ^ 2 := by
  have hc1 : (tajimaE1 n : ℝ) * (tajimaA1 n : ℝ) = (tajimaC1 n : ℝ) := by
    exact_mod_cast tajimaE1_mul hn
  have hc2 : (tajimaE2 n : ℝ) * ((tajimaA1 n : ℝ) ^ 2 + (tajimaA2 n : ℝ)) =
      (tajimaC2 n : ℝ) := by
    exact_mod_cast tajimaE2_mul hn
  have he : (∫ x, markedKingmanTajimaVarianceEstimate n x ∂Coalescent.markedKingmanLaw n θ) =
      ∫ x, (((tajimaE1 n : ℝ) - (tajimaE2 n : ℝ)) * markedKingmanSegregating n x +
        (tajimaE2 n : ℝ) * markedKingmanSegregating n x ^ 2) ∂Coalescent.markedKingmanLaw n θ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [markedKingmanTajimaVarianceEstimate]
    ring
  rw [he, integral_add ((integrable_markedKingmanSegregating n θ).const_mul _)
      ((integrable_markedKingmanSegregating_sq n θ).const_mul _),
    integral_const_mul, integral_const_mul, markedKingmanSegregating_mean hn θ,
    markedKingmanSegregating_second_moment hn θ]
  linear_combination (θ : ℝ) * hc1 + (θ : ℝ) ^ 2 * hc2

end Rhone.Statistics
