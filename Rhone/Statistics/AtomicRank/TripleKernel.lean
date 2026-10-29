/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.PolynomialSlices

/-! # The continuous symmetric three-iid polynomial observation kernel -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.AtomicRank

def sortedKernel (f : Coefficients) (a b c : ℝ) : ℝ :=
  let hi := max a (max b c)
  let lo := min a (min b c)
  (value f hi lo + value f hi (a + b + c - hi - lo)) / 2

def pairKernel (f : Coefficients) (z u v : ℝ) : ℝ :=
  if z ≤ max u v then
    (value f (max u v) z + value f (max u v) (min u v)) / 2
  else (value f z u + value f z v) / 2

lemma pairKernel_swap (f : Coefficients) (z u v : ℝ) :
    pairKernel f z u v = pairKernel f z v u := by
  simp only [pairKernel, max_comm u v, min_comm u v]
  split_ifs <;> ring

lemma sortedKernel_swap_last (f : Coefficients) (a b c : ℝ) :
    sortedKernel f a b c = sortedKernel f a c b := by
  unfold sortedKernel
  rw [max_comm b c, min_comm b c]
  have he : a + b + c = a + c + b := by ring
  rw [he]

lemma sortedKernel_swap_first (f : Coefficients) (a b c : ℝ) :
    sortedKernel f a b c = sortedKernel f b a c := by
  unfold sortedKernel
  rw [max_left_comm a b c, min_left_comm a b c, add_comm a b]

lemma pairKernel_eq_sorted_ordered (f : Coefficients) (z u v : ℝ) (huv : u ≤ v) :
    pairKernel f z u v = sortedKernel f z u v := by
  by_cases hzu : z ≤ u
  · have hzv := hzu.trans huv
    simp only [pairKernel, sortedKernel, max_eq_right huv, min_eq_left huv,
      ite_eq_left hzv, max_eq_right hzv, min_eq_left hzu]
    rw [show z + u + v - v - z = u by ring]
  · have huz : u ≤ z := le_of_not_ge hzu
    by_cases hzv : z ≤ v
    · simp only [pairKernel, sortedKernel, max_eq_right huv, min_eq_left huv,
        ite_eq_left hzv, max_eq_right hzv, min_eq_right huz]
      rw [show z + u + v - v - u = z by ring]
      ring
    · have hvz : v ≤ z := le_of_not_ge hzv
      simp only [pairKernel, sortedKernel, max_eq_right huv, min_eq_left huv,
        ite_eq_right hzv, max_eq_left hvz, min_eq_right huz]
      rw [show z + u + v - z - u = v by ring]

lemma pairKernel_eq_sorted (f : Coefficients) (z u v : ℝ) :
    pairKernel f z u v = sortedKernel f z u v := by
  rcases le_total u v with h | h
  · exact pairKernel_eq_sorted_ordered f z u v h
  · rw [pairKernel_swap, pairKernel_eq_sorted_ordered f z v u h, sortedKernel_swap_last]

lemma value_continuous (f : Coefficients) : Continuous (fun p : ℝ × ℝ => value f p.1 p.2) := by
  unfold value firstSlice
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, smul_eq_mul]
  fun_prop

lemma sortedKernel_continuous (f : Coefficients) :
    Continuous (fun p : ℝ × ℝ × ℝ => sortedKernel f p.1 p.2.1 p.2.2) := by
  have h1 : Continuous (fun p : ℝ × ℝ × ℝ =>
      (max p.1 (max p.2.1 p.2.2), min p.1 (min p.2.1 p.2.2))) := by fun_prop
  have h2 : Continuous (fun p : ℝ × ℝ × ℝ =>
      (max p.1 (max p.2.1 p.2.2), p.1 + p.2.1 + p.2.2 -
        max p.1 (max p.2.1 p.2.2) - min p.1 (min p.2.1 p.2.2))) := by fun_prop
  exact (((value_continuous f).comp h1).add ((value_continuous f).comp h2)).div_const 2

lemma pairKernel_of_value_form (f : Coefficients) (g : ℝ → ℝ)
    (hf : ∀ x y, value f x y = g x + 2 * g y) (z u v : ℝ) :
    pairKernel f z u v = g z + g u + g v := by
  rw [pairKernel]
  split_ifs with hz
  · rw [hf, hf]
    rcases le_total u v with h | h
    · rw [max_eq_right h, min_eq_left h]
      ring
    · rw [max_eq_left h, min_eq_right h]
      ring
  · rw [hf, hf]
    ring

end Rhone.Statistics.AtomicRank
