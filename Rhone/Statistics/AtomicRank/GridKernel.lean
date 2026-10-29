/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.KernelShape

/-! # A finite grid suffices to establish the all-degree jump-operator kernel -/

@[expose] public section

noncomputable section
open Polynomial
namespace Rhone.Statistics.AtomicRank

lemma jumpBasis_degree_le (h z : ℝ) (p q : ℕ) :
    (jumpBasis h z p q).natDegree ≤ p + q := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro v hv
  simp only [jumpBasis, coeff_sub, coeff_C_mul, coeff_add, coeff_X_pow]
  have hfirst : (p : ℝ) * z ^ (p - 1) *
      ((scaledPowerSum h q).coeff v + (if v = q + 1 then 1 else 0)) = 0 := by
    by_cases hp : p = 0
    · simp [hp]
    · have hq : q + 1 < v := by omega
      simp [scaledPowerSum_coeff_above h hq, (ne_of_gt hq)]
  have hsecond : (q : ℝ) * z ^ (q - 1) *
      ((if v = p + 1 then 1 else 0) - (h / 2) * (if v = p then 1 else 0)) = 0 := by
    by_cases hq : q = 0
    · simp [hq]
    · have hp1 : v ≠ p + 1 := by omega
      have hp0 : v ≠ p := by omega
      simp [hp1, hp0]
  rw [hfirst, hsecond, sub_self]

lemma jump_degree_le (h z : ℝ) {f : Coefficients} {n : ℕ} (hd : DegreeBound f n) :
    (jump h z f).natDegree ≤ n := by
  classical
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro v hv
  simp only [jump, Finsupp.linearCombination_apply, Finsupp.sum, finsetSum_coeff, coeff_smul]
  apply Finset.sum_eq_zero
  intro x hx
  have hb : x.1 + x.2 ≤ n := by
    apply le_of_not_gt
    intro hlt
    exact Finsupp.mem_support_iff.mp hx (hd x hlt)
  have hz : (jumpBasis h z x.1 x.2).coeff v = 0 :=
    coeff_eq_zero_of_natDegree_lt ((jumpBasis_degree_le h z x.1 x.2).trans_lt (hb.trans_lt hv))
  rw [hz, smul_zero]

theorem grid_jump_kernel_shape {h : ℝ} (hh : h ≠ 0) (n : ℕ) (f : Coefficients)
    (hd : DegreeBound f n)
    (hg : ∀ (z : ℝ) (i : Fin (n + 1)),
      (jump h z f).eval (((i.val : ℝ) + 1) * h) = 0) :
    (∀ p q : ℕ, 0 < p → 0 < q → f (p, q) = 0) ∧
      ∀ r : ℕ, 0 < r → f (0, r) = 2 * f (r, 0) := by
  apply jump_kernel_shape hh n f hd
  intro z
  exact polynomial_eq_zero_of_grid n hh (jump h z f) (jump_degree_le h z hd) (hg z)

end Rhone.Statistics.AtomicRank
