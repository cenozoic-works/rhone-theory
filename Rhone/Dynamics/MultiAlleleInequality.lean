/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Entropy inequalities for symmetric viability selection

Source: kingman1961_partial_averages, eq. (1), p. 78; burger2013_migration_selection, sec. 2.2, eq.
2.13. -/

@[expose] public section
namespace Rhone.Dynamics
open scoped BigOperators

noncomputable def selectionEntropyGap (x : ℝ) : ℝ := x * Real.log x - x + 1

theorem selectionEntropyGap_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ selectionEntropyGap x := by
  rcases hx.eq_or_lt with h | h
  · simp [← h, selectionEntropyGap]
  · have ht := Real.one_sub_inv_le_log_of_pos h
    have hm := mul_le_mul_of_nonneg_left ht h.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ h.ne'] at hm
    unfold selectionEntropyGap
    linarith

theorem selectionEntropyGap_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) :
    selectionEntropyGap x = 0 ↔ x = 1 := by
  constructor
  · intro hg
    by_contra hn
    rcases hx.eq_or_lt with h | h
    · simp [← h, selectionEntropyGap] at hg
    · have hi : x⁻¹ ≠ 1 := by simpa using hn
      have ht := Real.log_lt_sub_one_of_pos (inv_pos.mpr h) hi
      rw [Real.log_inv] at ht
      have hm := mul_lt_mul_of_pos_left ht h
      rw [mul_sub, mul_inv_cancel₀ h.ne', mul_one] at hm
      unfold selectionEntropyGap at hg
      nlinarith
  · rintro rfl
    simp [selectionEntropyGap]

theorem selection_entropy_sum_eq_zero_iff
    {ι : Type*} [Fintype ι] (p r : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 ≤ r i) :
    (∑ i, p i * selectionEntropyGap (r i)) = 0 ↔
      ∀ i, p i = 0 ∨ r i = 1 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hp i) (selectionEntropyGap_nonneg (hr i)))]
  simp only [Finset.mem_univ, true_implies, mul_eq_zero,
    selectionEntropyGap_eq_zero_iff (hr _)]

theorem selection_edge_entropy_bound
    {ι : Type*} [Fintype ι] (p r : ι → ℝ) (a : ι → ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 ≤ r i)
    (ha : ∀ i j, 0 ≤ a i j) (hsym : ∀ i j, a i j = a j i)
    (hp1 : ∑ i, p i = 1)
    (hrow : ∀ i, ∑ j, a i j = p i * r i)
    (hr1 : ∑ i, p i * r i = 1) :
    1 + 2 * (∑ i, p i * selectionEntropyGap (r i)) ≤
      ∑ i, ∑ j, a i j * r i * r j := by
  have hpos : ∀ i j, 0 < a i j → 0 < r i := by
    intro i j hij
    have hle : a i j ≤ ∑ k, a i k :=
      Finset.single_le_sum (fun k _ => ha i k) (Finset.mem_univ j)
    rw [hrow] at hle
    have hprod : 0 < p i * r i := hij.trans_le hle
    have hpositive := (mul_pos_iff.mp hprod).resolve_right (by
      intro hneg
      exact (not_lt_of_ge (hp i)) hneg.1) |>.2
    exact lt_of_le_of_ne (hr i) hpositive.ne
  have hpoint : ∀ i j,
      a i j * (1 + Real.log (r i) + Real.log (r j)) ≤ a i j * r i * r j := by
    intro i j
    rcases (ha i j).eq_or_lt with hz | hz
    · simp [← hz]
    · have hi := hpos i j hz
      have hj := hpos j i (by rwa [hsym j i])
      have ht := Real.log_le_sub_one_of_pos (mul_pos hi hj)
      rw [Real.log_mul hi.ne' hj.ne'] at ht
      have hm := mul_le_mul_of_nonneg_left ht (ha i j)
      nlinarith
  have htotal : (∑ i, ∑ j, a i j) = 1 := by simp_rw [hrow]; exact hr1
  have hleft : (∑ i, ∑ j, a i j * Real.log (r i)) =
      ∑ i, p i * r i * Real.log (r i) := by
    simp_rw [← Finset.sum_mul, hrow]
  have hright : (∑ i, ∑ j, a i j * Real.log (r j)) =
      ∑ i, p i * r i * Real.log (r i) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have hc : ∀ j, ∑ i, a i j = p j * r j := by
      intro j
      simp_rw [hsym _ j]
      exact hrow j
    simp_rw [hc]
  have hgap : (∑ i, p i * selectionEntropyGap (r i)) =
      (∑ i, p i * r i * Real.log (r i)) := by
    simp only [selectionEntropyGap, mul_add, mul_sub, mul_one,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, hr1, hp1, mul_assoc]
    ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint i j))
  simp only [mul_add, mul_one, Finset.sum_add_distrib] at hsum
  rw [htotal, hleft, hright] at hsum
  rw [hgap]
  linarith

end Rhone.Dynamics
