/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.KernelShape

/-! # Polynomial evaluation and an explicit value representation of the jump kernel -/

@[expose] public section

noncomputable section
open Polynomial
namespace Rhone.Statistics.AtomicRank

def firstSlice (y : ℝ) : Coefficients →ₗ[ℝ] ℝ[X] :=
  Finsupp.linearCombination ℝ (fun v : ℕ × ℕ => C (y ^ v.2) * X ^ v.1)

def secondSlice (x : ℝ) : Coefficients →ₗ[ℝ] ℝ[X] :=
  Finsupp.linearCombination ℝ (fun v : ℕ × ℕ => C (x ^ v.1) * X ^ v.2)

def value (f : Coefficients) (x y : ℝ) : ℝ := (firstSlice y f).eval x

lemma value_eq_second (f : Coefficients) (x y : ℝ) : value f x y = (secondSlice x f).eval y := by
  simp only [value, firstSlice, secondSlice, Finsupp.linearCombination_apply, Finsupp.sum,
    eval_finsetSum, eval_smul, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma value_add (f g : Coefficients) (x y : ℝ) :
    value (f + g) x y = value f x y + value g x y := by
  simp [value]

lemma value_single (p q : ℕ) (a x y : ℝ) :
    value (Finsupp.single (p, q) a) x y = a * x ^ p * y ^ q := by
  simp [value, firstSlice, mul_assoc, mul_comm]

lemma value_pure (r : ℕ) (a x y : ℝ) :
    value (pureCoefficients r a) x y = a * x ^ r + 2 * a * y ^ r := by
  rw [pureCoefficients, value_add, value_single, value_single]
  simp

lemma zero_degree_single {f : Coefficients} (hd : DegreeBound f 0) :
    f = Finsupp.single (0, 0) (f (0, 0)) := by
  ext v
  by_cases hv : v = (0, 0)
  · subst v
    simp
  · have hpos : 0 < v.1 + v.2 := by
      by_contra h
      have hv1 : v.1 = 0 := by omega
      have hv2 : v.2 = 0 := by omega
      exact hv (Prod.ext hv1 hv2)
    rw [hd v hpos]
    simp [hv]

theorem jump_kernel_value_form {h : ℝ} (hh : h ≠ 0) (n : ℕ) (f : Coefficients)
    (hd : DegreeBound f n) (hz : ∀ z : ℝ, jump h z f = 0) :
    ∃ g : ℝ[X], ∀ x y : ℝ, value f x y = g.eval x + 2 * g.eval y := by
  induction n generalizing f with
  | zero =>
      refine ⟨C (f (0, 0) / 3), ?_⟩
      intro x y
      conv_lhs => rw [zero_degree_single hd, value_single]
      simp only [pow_zero, mul_one, eval_C]
      ring
  | succ n ih =>
      let a := f (n + 1, 0)
      let g := f - pureCoefficients (n + 1) a
      have hgd : DegreeBound g n := strip_top_degree hh hd hz
      have hgz : ∀ z : ℝ, jump h z g = 0 := by
        intro z
        simp [g, map_sub, hz z, jump_pure hh]
      obtain ⟨P, hP⟩ := ih g hgd hgz
      refine ⟨P + C a * X ^ (n + 1), ?_⟩
      intro x y
      have hf : f = g + pureCoefficients (n + 1) a := by simp [g]
      conv_lhs => rw [hf, value_add, hP, value_pure]
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      ring

end Rhone.Statistics.AtomicRank
