/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.MoranSelectionSupport
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Field

/-!
# Selected Moran finite double sums

Source: altrock_traulsen2009, eq. (14). -/

@[expose] public section
namespace Rhone.MarkovChain.MoranSelectionSupport

open Finset

/-- Source: altrock_traulsen2009, eq. (14). -/
theorem triangle_sum (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ j ∈ Icc 1 (N - 1), ∑ k ∈ Icc j (N - 1), f k j) =
      ∑ k ∈ Icc 1 (N - 1), ∑ j ∈ Icc 1 k, f k j := by
  calc
    _ = ∑ j ∈ Icc 1 (N - 1), ∑ k ∈ Icc 1 (N - 1), if j ≤ k then f k j else 0 := by
      apply sum_congr rfl
      intro j hj
      have he : Icc j (N - 1) = (Icc 1 (N - 1)).filter (fun k => j ≤ k) := by
        ext k
        simp only [mem_Icc, mem_filter]
        simp only [mem_Icc] at hj
        omega
      rw [he, sum_filter]
    _ = ∑ k ∈ Icc 1 (N - 1), ∑ j ∈ Icc 1 (N - 1), if j ≤ k then f k j else 0 :=
      sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      have he : Icc 1 k = (Icc 1 (N - 1)).filter (fun j => j ≤ k) := by
        ext j
        simp only [mem_Icc, mem_filter]
        simp only [mem_Icc] at hk
        omega
      rw [he, sum_filter]

/-- Source: altrock_traulsen2009, eq. (14). -/
theorem geom_tail_ratio {N j : ℕ} {r : ℝ} (hr : 0 < r) (hj0 : 0 < j) (hjN : j < N) :
    (moranGeomSum r N - moranGeomSum r j) / (moranUp N r j * (r⁻¹) ^ j) =
      ∑ k ∈ Icc j (N - 1), (r⁻¹) ^ (k - j) / moranUp N r j := by
  have hs := sum_range_add_sum_Ico (fun k => (r⁻¹) ^ k) hjN.le
  change moranGeomSum r j + (∑ k ∈ Ico j N, (r⁻¹) ^ k) = moranGeomSum r N at hs
  have he : Ico j N = Icc j (N - 1) := by
    ext k
    simp only [mem_Ico, mem_Icc]
    omega
  rw [he] at hs
  have ht : moranGeomSum r N - moranGeomSum r j =
      ∑ k ∈ Icc j (N - 1), (r⁻¹) ^ k := by linarith
  rw [ht, sum_div]
  apply sum_congr rfl
  intro k hk
  simp only [mem_Icc] at hk
  have hp : (r⁻¹) ^ k = (r⁻¹) ^ (k - j) * (r⁻¹) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hk.1]
  have hq : (r⁻¹) ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero hr.ne')
  rw [hp]
  field_simp [hq]

/-- Source: altrock_traulsen2009, eq. (14). -/
theorem green_single_mutant (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (∑ j ∈ Icc 1 (N - 1), moranSelectionGreen N r 1 j) =
      moranFixProb N r 1 *
        (∑ k ∈ Icc 1 (N - 1), ∑ l ∈ Icc 1 k,
          (r⁻¹) ^ (k - l) / moranUp N r l) := by
  calc
    _ = moranFixProb N r 1 *
        (∑ j ∈ Icc 1 (N - 1),
          (moranGeomSum r N - moranGeomSum r j) / (moranUp N r j * (r⁻¹) ^ j)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      simp only [mem_Icc] at hj
      exact green_lower N r hj.1
    _ = moranFixProb N r 1 *
        (∑ j ∈ Icc 1 (N - 1), ∑ k ∈ Icc j (N - 1),
          (r⁻¹) ^ (k - j) / moranUp N r j) := by
      congr 1
      apply sum_congr rfl
      intro j hj
      simp only [mem_Icc] at hj
      exact geom_tail_ratio hr (by omega) (by omega)
    _ = _ := by rw [triangle_sum]

end Rhone.MarkovChain.MoranSelectionSupport
