/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DiploidGaussianApproximation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-! # Bounds on the symmetric Gaussian viability interaction -/

@[expose] public section
namespace Rhone.MarkovChain.DiploidMarginalSelection
open MeasureTheory GaussianHouseOfCards
open scoped Nat

theorem cosh_sub_one_le_half_sq_mul_cosh (t : ℝ) :
    Real.cosh t-1 ≤ t ^ 2/2*Real.cosh t := by
  have hs := (Real.hasSum_cosh t).summable
  have hshift := (summable_nat_add_iff 1).mpr hs
  have he : Real.cosh t-1 = ∑' n, t^(2*(n+1))/((2*(n+1)).factorial : ℝ) := by
    rw [Real.cosh_eq_tsum, hs.tsum_eq_zero_add]
    simp
  rw [he]
  calc
    _ ≤ ∑' n, (t ^ 2/2)*(t^(2*n)/((2*n).factorial : ℝ)) := by
      apply hshift.tsum_le_tsum _ (hs.mul_left (t ^ 2/2))
      intro n
      have hfac : 2*(2*n)! ≤ (2*(n+1))! := by
        have heq : 2*(n+1) = (2*n+1)+1 := by omega
        rw [heq, Nat.factorial_succ, Nat.factorial_succ]
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right ((2*n)!) (by nlinarith)
      have hfacR : (2 : ℝ)*((2*n).factorial : ℝ) ≤ ((2*(n+1)).factorial : ℝ) :=
    by exact_mod_cast hfac
      have hp : 0 ≤ t^(2*n) := by rw [pow_mul]; positivity
      have hnum : 0 ≤ t ^ 2*t^(2*n) := mul_nonneg (sq_nonneg t) hp
      have heq : 2*(n+1) = 2*n+2 := by omega
      calc
        _ = (t ^ 2*t^(2*n))/((2*(n+1)).factorial : ℝ) := by rw [heq, pow_add]; ring
        _ ≤ (t ^ 2*t^(2*n))/(2*((2*n).factorial : ℝ)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hfacR
        _ = _ := by ring
    _ = _ := by rw [hs.tsum_mul_left, ← Real.cosh_eq_tsum]

theorem gaussian_symmetric_interaction_identity (S a b : ℝ) :
    (gaussianFitness S (a+b)+gaussianFitness S (a-b))/2 =
      gaussianFitness S a*gaussianFitness S b*Real.cosh (a*b/S) := by
  unfold gaussianFitness
  rw [Real.cosh_eq]
  have hp : -(a+b) ^ 2/(2*S) = -a ^ 2/(2*S)+(-b ^ 2/(2*S))-a*b/S := by ring
  have hm : -(a-b) ^ 2/(2*S) = -a ^ 2/(2*S)+(-b ^ 2/(2*S))+a*b/S := by ring
  rw [hp, hm]
  simp only [Real.exp_add, Real.exp_sub]
  have hneg := Real.exp_neg (a*b/S)
  rw [hneg]
  ring

theorem gaussian_symmetric_interaction_error (S : ℝ) (hS : 0 < S) (a b : ℝ) :
    0 ≤ (gaussianFitness S (a+b)+gaussianFitness S (a-b))/2-
      gaussianFitness S a*gaussianFitness S b ∧
    (gaussianFitness S (a+b)+gaussianFitness S (a-b))/2-
      gaussianFitness S a*gaussianFitness S b ≤ a ^ 2*b ^ 2/(2*S ^ 2) := by
  have hp := gaussian_fitness_bounds S hS a
  have hq := gaussian_fitness_bounds S hS b
  have hid := gaussian_symmetric_interaction_identity S a b
  have havg : (gaussianFitness S (a+b)+gaussianFitness S (a-b))/2 ≤ 1 := by
    linarith [(gaussian_fitness_bounds S hS (a+b)).2,
      (gaussian_fitness_bounds S hS (a-b)).2]
  rw [hid]
  constructor
  · have := Real.one_le_cosh (a*b/S)
    nlinarith [mul_pos hp.1 hq.1]
  · have hb := mul_le_mul_of_nonneg_left (cosh_sub_one_le_half_sq_mul_cosh (a*b/S))
      (mul_pos hp.1 hq.1).le
    have hc : (a*b/S) ^ 2/2 ≥ 0 := by positivity
    have hd := mul_le_mul_of_nonneg_left havg hc
    rw [hid] at hd
    have he : (a*b/S) ^ 2/2 = a ^ 2*b ^ 2/(2*S ^ 2) := by ring
    rw [← he]
    nlinarith

end Rhone.MarkovChain.DiploidMarginalSelection
