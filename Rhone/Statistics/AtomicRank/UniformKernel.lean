/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.TripleKernel

/-! # Exact uniform-grid conditional kernels, including repeated atom draws -/

@[expose] public section

noncomputable section
open Polynomial
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

def atom (h : ℝ) (i : ℕ) : ℝ := ((i : ℝ) + 1) * h

def uniformKernel (N : ℕ) (h : ℝ) (f : Coefficients) (z : ℝ) : ℝ :=
  (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    pairKernel f z (atom h i) (atom h j)) / (N : ℝ) ^ 2

lemma symmetric_square_sum (N : ℕ) (a : ℕ → ℕ → ℝ)
    (hs : ∀ i j, a i j = a j i) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j) =
      ∑ i ∈ Finset.range N, (a i i + 2 * ∑ j ∈ Finset.range i, a i j) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib, ih]
      have he : (∑ i ∈ Finset.range n, a i n) = ∑ i ∈ Finset.range n, a n i :=
        Finset.sum_congr rfl fun i _ => hs i n
      rw [he]
      ring

lemma uniformKernel_triangle (N : ℕ) (h : ℝ) (f : Coefficients) (z : ℝ) :
    uniformKernel N h f z = (∑ i ∈ Finset.range N,
      (pairKernel f z (atom h i) (atom h i) +
        2 * ∑ j ∈ Finset.range i, pairKernel f z (atom h i) (atom h j))) / (N : ℝ)^2 := by
  unfold uniformKernel
  rw [symmetric_square_sum N _ (fun i j => pairKernel_swap f z (atom h i) (atom h j))]

lemma uniformKernel_of_value_form {N : ℕ} (hN : 0 < N) (h : ℝ)
    (f : Coefficients) (g : ℝ → ℝ)
    (hf : ∀ x y, value f x y = g x + 2 * g y) (z : ℝ) :
    uniformKernel N h f z = g z + 2 * ((∑ i ∈ Finset.range N, g (atom h i)) / (N : ℝ)) := by
  unfold uniformKernel
  simp_rw [pairKernel_of_value_form f g hf, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma atom_mono {h : ℝ} (hh : 0 ≤ h) {i j : ℕ} (hij : i ≤ j) : atom h i ≤ atom h j := by
  unfold atom
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hij) hh

theorem constant_kernel_of_zero_jump {N : ℕ} (hN : 0 < N) {h : ℝ} (hh : h ≠ 0)
    (n : ℕ) (f : Coefficients) (hd : DegreeBound f n)
    (hj : ∀ z : ℝ, jump h z f = 0) (c : ℝ)
    (hc : ∀ z : ℝ, uniformKernel N h f z = c) :
    ∃ d : ℝ, ∀ x y : ℝ, value f x y = d := by
  obtain ⟨g, hg⟩ := jump_kernel_value_form hh n f hd hj
  let b := 2 * ((∑ i ∈ Finset.range N, g.eval (atom h i)) / (N : ℝ))
  have he : ∀ z : ℝ, g.eval z = c - b := by
    intro z
    have hk := uniformKernel_of_value_form hN h f g.eval hg z
    rw [hc z] at hk
    dsimp [b]
    linarith
  refine ⟨3 * (c - b), ?_⟩
  intro x y
  rw [hg, he, he]
  ring

end Rhone.Statistics.AtomicRank
