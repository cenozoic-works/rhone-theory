/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.HistogramBinAffine
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact integration formulas for affine histogram pieces -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.BinnedPanLaw

def powerIntegral (p : ℕ) (a b : ℝ) : ℝ := (b ^ (p + 1) - a ^ (p + 1)) / (p + 1)

theorem power_integral (p : ℕ) (a b : ℝ) :
    (∫ x in a..b, x ^ p) = powerIntegral p a b := integral_pow p

theorem affine_weighted_integral (p : ℕ) (A B a b : ℝ) :
    (∫ x in a..b, x ^ p * (A + B * x)) =
      A * powerIntegral p a b + B * powerIntegral (p + 1) a b := by
  have he : (fun x : ℝ => x ^ p * (A + B * x)) =
      fun x => A * x ^ p + B * x ^ (p + 1) := by
    funext x
    rw [pow_succ]
    ring
  rw [he, intervalIntegral.integral_add
    ((show Continuous (fun x : ℝ => A * x ^ p) by fun_prop).intervalIntegrable _ _)
    ((show Continuous (fun x : ℝ => B * x ^ (p + 1)) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    power_integral, power_integral]

theorem histogram_bin_integral {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) (i : Fin n)
    (p : ℕ) {a b : ℝ} (hab : a ≤ b)
    (ha : (i : ℝ) / n ≤ a) (hb : b ≤ ((i : ℝ) + 1) / n) :
    (∫ x in a..b, x ^ p * histogramCDF w x) =
      binIntercept w i * powerIntegral p a b +
        binSlope w i * powerIntegral (p + 1) a b := by
  rw [← affine_weighted_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  dsimp only
  rw [histogramCDF_piece hn w i ⟨ha.trans hx.1, hx.2.trans hb⟩]

theorem integral_grid_sum {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (0 : ℝ)..1, f x) =
      ∑ i : Fin n, ∫ x in (i : ℝ) / n..((i : ℝ) + 1) / n, f x := by
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) / n) (n := n)
    (f := f) (μ := volume) (fun _ _ => hf.intervalIntegrable _ _)
  rw [← Fin.sum_univ_eq_sum_range] at he
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simpa only [Nat.cast_zero, zero_div, div_self hn', Nat.cast_add, Nat.cast_one] using he.symm

end Rhone.Statistics.BinnedPanLaw
