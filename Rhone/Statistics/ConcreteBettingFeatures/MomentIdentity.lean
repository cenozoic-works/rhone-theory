/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcreteBettingFeatures.Coefficients

/-! # Exact expectation identity from the 95 kernel-checked integer coefficients -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ConcreteBettingFeatures
open ConcretePatternMoments
local notation "mult" => ConcretePatternMoments.multiplicity

def targetMoment (i : Fin 5) (M : Fin 19 → ℝ) : ℝ :=
  (∑ j, (targetNumerator i j : ℝ) * M j) / 3

theorem weighted_moment_identity (i : Fin 5) (M : Fin 19 → ℝ) :
    (∑ r : Row, mult r.1 * mult r.2.1 * mult r.2.2 * feature i r *
      ((∑ j : Fin 19, (coefficient r j : ℝ) * M j) / 786432)) = targetMoment i M := by
  have hc (j : Fin 19) :
      (∑ r : Row, mult r.1 * mult r.2.1 * mult r.2.2 *
        (numerator i r : ℝ) * (coefficient r j : ℝ)) =
          63700992 * (targetNumerator i j : ℝ) := by
    have h := moment_coefficient_certificate i j
    unfold ConcretePatternMoments.multiplicity
    exact_mod_cast h
  have he (r : Row) :
      mult r.1 * mult r.2.1 * mult r.2.2 * feature i r *
        ((∑ j : Fin 19, (coefficient r j : ℝ) * M j) / 786432) =
      ∑ j : Fin 19, (mult r.1 * mult r.2.1 * mult r.2.2 *
        (numerator i r : ℝ) * (coefficient r j : ℝ)) * M j / (243 * 786432) := by
    simp only [feature, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_div, ← Finset.sum_mul, hc]
  unfold targetMoment
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Rhone.Statistics.ConcreteBettingFeatures
