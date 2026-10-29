/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePatternMoments.Polynomial
public import Rhone.Statistics.ThreeSiteSeparator.BlockExpectations

/-! # Polynomial bridge to the observer at every real clock -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ConcretePatternMoments
open ThreeTipSites ThreeSiteSeparator SingleSiteChannel

def firstDecay (k : ℝ) (t : ℝ × ℝ) : ℝ := Real.exp (-(k / 2) * t.1)
def lastDecay (k : ℝ) (t : ℝ × ℝ) : ℝ := Real.exp (-(k / 2) * (t.1 + t.2))

theorem decay_identities (k : ℝ) (t : ℝ × ℝ) :
    firstDecay k t ^ 2 = Real.exp (-k * t.1) ∧
    lastDecay k t ^ 2 = Real.exp (-k * (t.1 + t.2)) ∧
    firstDecay k t * lastDecay k t ^ 2 = secondMomentKernel k t := by
  unfold firstDecay lastDecay secondMomentKernel
  constructor
  · rw [sq, ← Real.exp_add]; congr 1; ring
  constructor
  · rw [sq, ← Real.exp_add]; congr 1; ring
  · rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem conditional_row_polynomial (k : ℝ) (t : ℝ × ℝ) (x : Panel 4 3) :
    conditional (uniformBlockRoots 4 3 (by norm_num)) k t x =
      rowPolynomial (rowOf x) (firstDecay k t) (lastDecay k t) := by
  obtain ⟨h1, h2, h3⟩ := decay_identities k t
  unfold conditional fixedTopology
  simp only [uniformBlockRoots, Fin.prod_univ_three]
  norm_num only [Nat.cast_ofNat]
  simp_rw [site_category]
  unfold rowPolynomial rowOf
  rw [h3, h1, h2]
  ring

def scaledKernel (k : ℝ) (p q : ℕ) (t : ℝ × ℝ) : ℝ :=
  Real.exp (-(k / 2) * (((p : ℝ) + q) * t.1 + q * t.2))

theorem monomial_scaled_kernel (k : ℝ) (p q : ℕ) (t : ℝ × ℝ) :
    firstDecay k t ^ p * lastDecay k t ^ q = scaledKernel k p q t := by
  unfold firstDecay lastDecay scaledKernel
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem conditional_moment_expansion (k : ℝ) (t : ℝ × ℝ) (x : Panel 4 3) :
    conditional (uniformBlockRoots 4 3 (by norm_num)) k t x =
      (∑ j : Fin 19, (coefficient (rowOf x) j : ℝ) *
        scaledKernel k (exponents j).1 (exponents j).2 t) / 786432 := by
  rw [conditional_row_polynomial, row_polynomial_expansion]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, monomial_scaled_kernel]

end Rhone.Statistics.ConcretePatternMoments
