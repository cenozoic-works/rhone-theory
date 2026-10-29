/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.PolynomialPatches
public import Rhone.Statistics.AtomicRank.GridKernel

/-! # Adjacent conditional-kernel patches give the exact interpolated jump operator -/

@[expose] public section

noncomputable section
open Polynomial
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

lemma jumpBasis_eval_atom {h : ℝ} (hh : h ≠ 0) (z : ℝ) (i p q : ℕ) :
    (jumpBasis h z p q).eval (atom h i) = h *
      (((i : ℝ) + 1) * ((atom h i)^q * (p : ℝ) * z^(p-1)) +
        (∑ j ∈ Finset.range i, (atom h j)^q * (p : ℝ) * z^(p-1)) -
        ((i : ℝ) + 1/2) * ((atom h i)^p * (q : ℝ) * z^(q-1))) := by
  have hs : (scaledPowerSum h q).eval (atom h i) =
      h * ∑ j ∈ Finset.range i, (atom h j)^q := by
    simpa [atom] using scaledPowerSum_eval_succ_grid hh q i
  simp only [jumpBasis, eval_sub, eval_mul, eval_C, eval_add, eval_pow, eval_X]
  rw [hs, ← Finset.sum_mul, ← Finset.sum_mul]
  simp only [pow_succ]
  unfold atom
  ring

lemma jump_eval_atom {h : ℝ} (hh : h ≠ 0) (z : ℝ) (i : ℕ) (f : Coefficients) :
    (jump h z f).eval (atom h i) = h *
      (((i : ℝ) + 1) * ((firstSlice (atom h i) f).derivative.eval z) +
        (∑ j ∈ Finset.range i, (firstSlice (atom h j) f).derivative.eval z) -
        ((i : ℝ) + 1/2) * ((secondSlice (atom h i) f).derivative.eval z)) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp [jump, firstSlice, secondSlice]
  | add f g hf hg =>
      simp only [map_add, eval_add, Finset.sum_add_distrib]
      linear_combination hf + hg
  | single v a =>
      rcases v with ⟨p, q⟩
      simp only [jump, firstSlice, secondSlice, Finsupp.linearCombination_single,
        derivative_smul, derivative_C_mul_X_pow, eval_smul, eval_mul, eval_C,
        eval_pow, eval_X, smul_eq_mul]
      rw [jumpBasis_eval_atom hh]
      rw [← Finset.mul_sum]
      ring

lemma gapPolynomial_step {N i : ℕ} (hi : i < N) (h : ℝ) (f : Coefficients) :
    gapPolynomial N (i+1) h f - gapPolynomial N i h f =
      lowerPolynomial h i f - upperPolynomial h i f := by
  unfold gapPolynomial
  rw [← Finset.sum_sub_distrib]
  have hs : (∑ j ∈ Finset.range N,
      ((if j < i+1 then lowerPolynomial h j f else upperPolynomial h j f) -
        (if j < i then lowerPolynomial h j f else upperPolynomial h j f))) =
      ∑ j ∈ Finset.range N,
        if j = i then lowerPolynomial h i f - upperPolynomial h i f else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases he : j = i
    · subst j
      simp
    · have hiff : j < i + 1 ↔ j < i := by omega
      simp only [hiff, ite_eq_right he]
      split_ifs <;> simp
  rw [hs]
  simp [Finset.mem_range.mpr hi]

lemma adjacent_derivative_eval {h : ℝ} (hh : h ≠ 0) {N i : ℕ} (hi : i < N)
    (f : Coefficients) (z : ℝ) :
    h * ((gapPolynomial N (i+1) h f).derivative.eval z -
      (gapPolynomial N i h f).derivative.eval z) = (jump h z f).eval (atom h i) := by
  have he := congrArg (fun P : ℝ[X] => P.derivative.eval z) (gapPolynomial_step hi h f)
  simp only [derivative_sub, eval_sub] at he
  rw [he, jump_eval_atom hh]
  simp only [lowerPolynomial, upperPolynomial, derivative_add, derivative_C_mul,
    derivative_sum, derivative_C, eval_add, eval_mul, eval_C, eval_finsetSum, add_zero]

end Rhone.Statistics.AtomicRank
