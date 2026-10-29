/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.UniformKernel

/-! # The true grid conditional kernel is polynomial on every inter-atom interval -/

@[expose] public section

noncomputable section
open Polynomial Set
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

def lowerPolynomial (h : ℝ) (i : ℕ) (f : Coefficients) : ℝ[X] :=
  C ((i : ℝ) + 1) * firstSlice (atom h i) f +
    ∑ j ∈ Finset.range i, firstSlice (atom h j) f

def upperPolynomial (h : ℝ) (i : ℕ) (f : Coefficients) : ℝ[X] :=
  C ((i : ℝ) + 1 / 2) * secondSlice (atom h i) f +
    C ((∑ j ∈ Finset.range i, value f (atom h i) (atom h j)) +
      value f (atom h i) (atom h i) / 2)

def gapPolynomial (N k : ℕ) (h : ℝ) (f : Coefficients) : ℝ[X] :=
  ∑ i ∈ Finset.range N, if i < k then lowerPolynomial h i f else upperPolynomial h i f

lemma triangle_lower {h z : ℝ} (hh : 0 ≤ h) (i : ℕ) (f : Coefficients)
    (hz : atom h i < z) :
    pairKernel f z (atom h i) (atom h i) +
      2 * (∑ j ∈ Finset.range i, pairKernel f z (atom h i) (atom h j)) =
        (lowerPolynomial h i f).eval z := by
  have hdiag : pairKernel f z (atom h i) (atom h i) = value f z (atom h i) := by
    simp [pairKernel, not_le.mpr hz]
  have hsum : (∑ j ∈ Finset.range i, pairKernel f z (atom h i) (atom h j)) =
      ∑ j ∈ Finset.range i, (value f z (atom h i) + value f z (atom h j)) / 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have ha := atom_mono hh (Finset.mem_range.mp hj).le
    simp [pairKernel, max_eq_left ha, not_le.mpr hz]
  rw [hdiag, hsum, ← Finset.sum_div, Finset.sum_add_distrib]
  simp only [lowerPolynomial, eval_add, eval_mul, eval_C, eval_finsetSum,
    value, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

lemma triangle_upper {h z : ℝ} (hh : 0 ≤ h) (i : ℕ) (f : Coefficients)
    (hz : z ≤ atom h i) :
    pairKernel f z (atom h i) (atom h i) +
      2 * (∑ j ∈ Finset.range i, pairKernel f z (atom h i) (atom h j)) =
        (upperPolynomial h i f).eval z := by
  have hdiag : pairKernel f z (atom h i) (atom h i) =
      (value f (atom h i) z + value f (atom h i) (atom h i)) / 2 := by
    simp [pairKernel, hz]
  have hsum : (∑ j ∈ Finset.range i, pairKernel f z (atom h i) (atom h j)) =
      ∑ j ∈ Finset.range i, (value f (atom h i) z + value f (atom h i) (atom h j)) / 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have ha := atom_mono hh (Finset.mem_range.mp hj).le
    simp [pairKernel, max_eq_left ha, min_eq_right ha, hz]
  rw [hdiag, hsum, ← Finset.sum_div, Finset.sum_add_distrib]
  simp only [upperPolynomial, eval_add, eval_mul, eval_C, ← value_eq_second,
     Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma uniformKernel_on_gap {h z : ℝ} (hh : 0 < h) (N k : ℕ) (f : Coefficients)
    (hz : z ∈ Ioo ((k : ℝ) * h) (((k : ℝ) + 1) * h)) :
    uniformKernel N h f z = (gapPolynomial N k h f).eval z / (N : ℝ)^2 := by
  rw [uniformKernel_triangle, gapPolynomial, eval_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hik : i < k
  · rw [ite_eq_left hik]
    apply triangle_lower hh.le
    have ht : atom h i ≤ (k : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hik) hh.le
    exact ht.trans_lt hz.1
  · rw [ite_eq_right hik]
    apply triangle_upper hh.le
    have ht : ((k : ℝ) + 1) * h ≤ atom h i := by
      apply mul_le_mul_of_nonneg_right _ hh.le
      exact_mod_cast Nat.succ_le_succ (le_of_not_gt hik)
    exact hz.2.le.trans ht

lemma gapPolynomial_constant {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    (f : Coefficients) (c : ℝ)
    (hc : ∀ z ∈ Ioo (0 : ℝ) (((N : ℝ) + 1) * h), uniformKernel N h f z = c)
    {k : ℕ} (hk : k ≤ N) : gapPolynomial N k h f = C (c * (N : ℝ)^2) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hwidth : (k : ℝ) * h < ((k : ℝ) + 1) * h := by nlinarith
  apply (Set.Ioo_infinite hwidth).mono
  intro z hz
  have h0 : 0 ≤ (k : ℝ) * h := by positivity
  have htop : ((k : ℝ) + 1) * h ≤ ((N : ℝ) + 1) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hk) hh.le
  have he := uniformKernel_on_gap hh N k f hz
  rw [hc z ⟨h0.trans_lt hz.1, hz.2.trans_le htop⟩] at he
  have hn : (N : ℝ)^2 ≠ 0 := by positivity
  simpa only [Set.mem_ofPred_eq, eval_C] using (div_eq_iff hn).mp he.symm

end Rhone.Statistics.AtomicRank
