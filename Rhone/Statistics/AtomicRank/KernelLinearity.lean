/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.ConditionalRigidity

/-! # Linearity of the conditional kernel in the polynomial feature -/

@[expose] public section

noncomputable section
open Polynomial
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

lemma value_smul (a : ℝ) (f : Coefficients) (x y : ℝ) :
    value (a • f) x y = a * value f x y := by
  simp [value, smul_eq_mul]

lemma pairKernel_add (f g : Coefficients) (z u v : ℝ) :
    pairKernel (f + g) z u v = pairKernel f z u v + pairKernel g z u v := by
  simp only [pairKernel, value_add]
  split_ifs <;> ring

lemma pairKernel_smul (a : ℝ) (f : Coefficients) (z u v : ℝ) :
    pairKernel (a • f) z u v = a * pairKernel f z u v := by
  simp only [pairKernel, value_smul]
  split_ifs <;> ring

lemma uniformKernel_add (N : ℕ) (h : ℝ) (f g : Coefficients) (z : ℝ) :
    uniformKernel N h (f + g) z = uniformKernel N h f z + uniformKernel N h g z := by
  simp [uniformKernel, pairKernel_add, Finset.sum_add_distrib, add_div]

lemma uniformKernel_smul (N : ℕ) (h a : ℝ) (f : Coefficients) (z : ℝ) :
    uniformKernel N h (a • f) z = a * uniformKernel N h f z := by
  simp only [uniformKernel, pairKernel_smul, ← Finset.mul_sum]
  ring

lemma uniformKernel_zero (N : ℕ) (h z : ℝ) : uniformKernel N h 0 z = 0 := by
  simp [uniformKernel, pairKernel, value]

lemma uniformKernel_sum {ι : Type*} (s : Finset ι) (N : ℕ) (h : ℝ)
    (f : ι → Coefficients) (z : ℝ) :
    uniformKernel N h (∑ i ∈ s, f i) z = ∑ i ∈ s, uniformKernel N h (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [uniformKernel_zero]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, uniformKernel_add, ih]

lemma uniformKernel_linear_combination {d : ℕ} (N : ℕ) (h : ℝ)
    (a : Fin d → ℝ) (f : Fin d → Coefficients) (z : ℝ) :
    uniformKernel N h (∑ i, a i • f i) z = ∑ i, a i * uniformKernel N h (f i) z := by
  rw [uniformKernel_sum]
  simp_rw [uniformKernel_smul]

lemma value_linear_combination {d : ℕ} (a : Fin d → ℝ) (f : Fin d → Coefficients)
    (x y : ℝ) : value (∑ i, a i • f i) x y = ∑ i, a i * value (f i) x y := by
  simp [value, map_sum, eval_finsetSum, smul_eq_mul]

lemma degreeBound_linear_combination {n d : ℕ} (a : Fin d → ℝ)
    (f : Fin d → Coefficients) (hf : ∀ i, DegreeBound (f i) n) :
    DegreeBound (∑ i, a i • f i) n := by
  intro v hv
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [hf i v hv, mul_zero]

end Rhone.Statistics.AtomicRank
