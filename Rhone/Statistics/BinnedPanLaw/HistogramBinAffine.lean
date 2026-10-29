/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.CDF

/-! # Exact affine formulas on each histogram bin -/

@[expose] public section

noncomputable section
open Set
open scoped BigOperators
namespace Rhone.Statistics.BinnedPanLaw
open AtomicSmoothing
variable {n : ℕ}

def cumulative (w : Fin n → ℝ) (i : Fin n) : ℝ := ∑ j with j < i, w j

def binSlope (w : Fin n → ℝ) (i : Fin n) : ℝ := n * w i

def binIntercept (w : Fin n → ℝ) (i : Fin n) : ℝ := cumulative w i - w i * i

theorem histogramCDF_piece (hn : 0 < n) (w : Fin n → ℝ) (i : Fin n) {x : ℝ}
    (hx : x ∈ Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) :
    histogramCDF w x = binIntercept w i + binSlope w i * x := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hxl : (i : ℝ) ≤ n * x := by
    have h := (div_le_iff₀ hn').mp hx.1
    nlinarith
  have hxu : (n : ℝ) * x ≤ i + 1 := by
    have h := (le_div_iff₀ hn').mp hx.2
    nlinarith
  have he (j : Fin n) : w j * clip (n * x - j) =
      (if j < i then w j else 0) + (if j = i then w i * (n * x - i) else 0) := by
    by_cases hji : j < i
    · have hj : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
      rw [ite_eq_left hji, ite_eq_right (ne_of_lt hji), clip_one (by linarith)]
      ring
    · by_cases hji' : j = i
      · subst j
        rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl, clip_self (by linarith) (by linarith)]
        ring
      · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hji')
        have hj : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
        rw [ite_eq_right hji, ite_eq_right hji', clip_zero (by linarith)]
        ring
  unfold histogramCDF
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter]
  unfold binIntercept binSlope cumulative
  ring

end Rhone.Statistics.BinnedPanLaw
