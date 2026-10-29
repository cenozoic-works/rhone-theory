/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SegregatingMoments

/-!
# Mean and variance of Watterson's estimator under the marked law

Source: watterson1975, p. 258, eq. (1.4a)–(1.5a); durrett2008, Thm 1.22; tajima1989, p. 585, eq.
(1)–(5). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Rhone.Combinatorics MarkovChain Probability
open scoped NNReal

/-- Source: watterson1975, p. 258, eq. (1.4a); durrett2008, Thm 1.22. -/
theorem markedKingmanWatterson_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    (∫ x, markedKingmanWatterson n x ∂Coalescent.markedKingmanLaw n θ) = (θ : ℝ) := by
  have ha1 : (tajimaA1 n : ℝ) ≠ 0 := by
    have hq : (0 : ℚ) < tajimaA1 n := zero_lt_harmonic (by omega)
    exact ne_of_gt (by exact_mod_cast hq)
  unfold markedKingmanWatterson
  rw [integral_div, markedKingmanSegregating_mean hn θ]
  exact mul_div_cancel_right₀ (θ : ℝ) ha1

/-- Source: watterson1975, p. 258, eq. (1.5a); durrett2008, Thm 1.22. -/
theorem markedKingmanWatterson_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanWatterson n) (Coalescent.markedKingmanLaw n θ) =
      (θ : ℝ) / (tajimaA1 n : ℝ) +
        (θ : ℝ) ^ 2 * (tajimaA2 n : ℝ) / (tajimaA1 n : ℝ) ^ 2 := by
  have ha1 : (tajimaA1 n : ℝ) ≠ 0 := by
    have hq : (0 : ℚ) < tajimaA1 n := zero_lt_harmonic (by omega)
    exact ne_of_gt (by exact_mod_cast hq)
  change variance (fun x => markedKingmanSegregating n x / (tajimaA1 n : ℝ))
    (Coalescent.markedKingmanLaw n θ) = _
  simp only [div_eq_mul_inv]
  rw [variance_mul_const, markedKingmanSegregating_variance hn θ]
  field_simp [ha1]

end Rhone.Statistics
