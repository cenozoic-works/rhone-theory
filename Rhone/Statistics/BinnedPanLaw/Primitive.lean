/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.Integrals
public import Rhone.Statistics.ThreeSiteSeparator.WeightedPrimitive

/-! # Exact weighted CDF primitive on every bin -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.BinnedPanLaw
open ThreeSiteSeparator
variable {n : ℕ}

def cellPrimitive (w : Fin n → ℝ) (p : ℕ) (i : Fin n) (x : ℝ) : ℝ :=
  binIntercept w i * powerIntegral p ((i : ℝ) / n) x +
    binSlope w i * powerIntegral (p + 1) ((i : ℝ) / n) x

def prefixPrimitive (w : Fin n → ℝ) (p j : ℕ) : ℝ :=
  ∑ i : Fin n with i.val < j, cellPrimitive w p i (((i : ℝ) + 1) / n)

theorem prefix_primitive_succ (w : Fin n → ℝ) (p j : ℕ) (hj : j < n) :
    prefixPrimitive w p (j + 1) = prefixPrimitive w p j +
      cellPrimitive w p ⟨j, hj⟩ (((j : ℝ) + 1) / n) := by
  classical
  have he : (Finset.univ.filter (fun i : Fin n => i.val < j + 1)) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun i : Fin n => i.val < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases he : i.val = j
      · left; exact Fin.ext he
      · right; omega
    · rintro (rfl | h)
      · exact Nat.lt_succ_self j
      · exact Nat.lt_succ_of_lt h
  unfold prefixPrimitive
  rw [he, Finset.sum_insert (by simp)]
  ring

theorem prefix_primitive_integral (hn : 0 < n) (w : Fin n → ℝ) (p j : ℕ) (hj : j ≤ n) :
    (∫ x in (0 : ℝ)..(j : ℝ) / n, x ^ p * histogramCDF w x) = prefixPrimitive w p j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : Continuous (fun x : ℝ => x ^ p * histogramCDF w x) :=
    (continuous_id.pow p).mul (histogramCDF_lipschitz w).choose_spec.continuous
  induction j with
  | zero => simp [prefixPrimitive]
  | succ j ih =>
    have hjn : j < n := by omega
    rw [prefix_primitive_succ w p j hjn, Nat.cast_add, Nat.cast_one,
      ← intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable 0 ((j : ℝ) / n))
        (hc.intervalIntegrable ((j : ℝ) / n) (((j : ℝ) + 1) / n)), ih (by omega)]
    congr 1
    exact histogram_bin_integral hn w ⟨j, hjn⟩ p
      (div_le_div_of_nonneg_right (by linarith) hn'.le) le_rfl le_rfl

theorem weighted_primitive_piece (hn : 0 < n) (w : Fin n → ℝ) (p : ℕ) (i : Fin n)
    {x : ℝ} (hx : x ∈ Icc ((i : ℝ) / n) (((i : ℝ) + 1) / n)) :
    weightedPrimitive p (histogramCDF w) x = prefixPrimitive w p i.val + cellPrimitive w p i x := by
  have hc : Continuous (fun x : ℝ => x ^ p * histogramCDF w x) :=
    (continuous_id.pow p).mul (histogramCDF_lipschitz w).choose_spec.continuous
  unfold weightedPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 ((i : ℝ) / n)) (hc.intervalIntegrable ((i : ℝ) / n) x),
    prefix_primitive_integral hn w p i.val i.isLt.le]
  congr 1
  exact histogram_bin_integral hn w i p hx.1 le_rfl hx.2

end Rhone.Statistics.BinnedPanLaw
