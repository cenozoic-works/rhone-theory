/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.AdjacentGaps

/-! # Rigidity of the three-iid uniform-grid conditional polynomial kernel -/

@[expose] public section

noncomputable section
open Polynomial Set
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

lemma constant_uniformKernel_zero_jump {h : ℝ} (hh : 0 < h) (n : ℕ)
    (f : Coefficients) (hd : DegreeBound f n) (c : ℝ)
    (hc : ∀ z ∈ Ioo (0 : ℝ) ((((n + 1 : ℕ) : ℝ) + 1) * h),
      uniformKernel (n + 1) h f z = c) :
    ∀ z : ℝ, jump h z f = 0 := by
  intro z
  apply polynomial_eq_zero_of_grid n hh.ne' (jump h z f) (jump_degree_le h z hd)
  intro i
  have hleft := gapPolynomial_constant (Nat.succ_pos n) hh f c hc
    (k := i.val + 1) (Nat.succ_le_of_lt i.isLt)
  have hright := gapPolynomial_constant (Nat.succ_pos n) hh f c hc (k := i.val) i.isLt.le
  have he := adjacent_derivative_eval hh.ne' i.isLt f z
  rw [hleft, hright, derivative_C, eval_zero, sub_self, mul_zero] at he
  exact he.symm

theorem conditional_kernel_rigidity {h : ℝ} (hh : 0 < h) (n : ℕ)
    (f : Coefficients) (hd : DegreeBound f n) (c : ℝ)
    (hc : ∀ z ∈ Ioo (0 : ℝ) ((((n + 1 : ℕ) : ℝ) + 1) * h),
      uniformKernel (n + 1) h f z = c) :
    ∃ d : ℝ, ∀ x y : ℝ, value f x y = d := by
  have hj := constant_uniformKernel_zero_jump hh n f hd c hc
  obtain ⟨g, hg⟩ := jump_kernel_value_form hh.ne' n f hd hj
  let b := 2 * ((∑ i ∈ Finset.range (n + 1), g.eval (atom h i)) / ((n + 1 : ℕ) : ℝ))
  have he : g = C (c - b) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hwidth : (0 : ℝ) < ((((n + 1 : ℕ) : ℝ) + 1) * h) := by positivity
    apply (Set.Ioo_infinite hwidth).mono
    intro z hz
    have hk := uniformKernel_of_value_form (Nat.succ_pos n) h f g.eval hg z
    rw [hc z hz] at hk
    change g.eval z = (C (c - b)).eval z
    rw [eval_C]
    dsimp [b]
    linarith
  refine ⟨3 * (c - b), ?_⟩
  intro x y
  rw [hg, he]
  simp only [eval_C]
  ring

theorem unit_interval_conditional_rigidity (n : ℕ) (f : Coefficients)
    (hd : DegreeBound f n) (c : ℝ)
    (hc : ∀ z ∈ Ioo (0 : ℝ) 1, uniformKernel (n + 1) (1 / ((n : ℝ) + 2)) f z = c) :
    ∃ d : ℝ, ∀ x y : ℝ, value f x y = d := by
  have hh : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  apply conditional_kernel_rigidity hh n f hd c
  have ht : ((((n + 1 : ℕ) : ℝ) + 1) * (1 / ((n : ℝ) + 2))) = 1 := by
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  simpa only [ht] using hc

end Rhone.Statistics.AtomicRank
