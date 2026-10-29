/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.LeadingOperator
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Linear jump operators on finite bivariate coefficient arrays -/

@[expose] public section

noncomputable section
open Polynomial
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

abbrev Coefficients := (ℕ × ℕ) →₀ ℝ

def DegreeBound (f : Coefficients) (n : ℕ) : Prop :=
  ∀ v : ℕ × ℕ, n < v.1 + v.2 → f v = 0

def jump (h z : ℝ) : Coefficients →ₗ[ℝ] ℝ[X] :=
  Finsupp.linearCombination ℝ (fun v : ℕ × ℕ => jumpBasis h z v.1 v.2)

def jumpCoefficient (h : ℝ) (v : ℕ) : Coefficients →ₗ[ℝ] ℝ[X] :=
  Finsupp.linearCombination ℝ (fun w : ℕ × ℕ => jumpCoefficientBasis h v w.1 w.2)

lemma jump_coeff (h z : ℝ) (f : Coefficients) (v : ℕ) :
    (jump h z f).coeff v = (jumpCoefficient h v f).eval z := by
  simp only [jump, jumpCoefficient, Finsupp.linearCombination_apply, Finsupp.sum,
    finsetSum_coeff, coeff_smul, eval_finsetSum, eval_smul, jumpBasis_coeff]

lemma sum_select (f : Coefficients) (a : ℕ × ℕ) (r : ℝ) :
    (∑ x ∈ f.support, f x * (if x = a then r else 0)) = f a * r := by
  classical
  by_cases ha : a ∈ f.support
  · simp [mul_ite, ha]
  · have hz : f a = 0 := Finsupp.notMem_support_iff.mp ha
    simp [mul_ite, ha, hz]

lemma jumpCoefficient_top {h : ℝ} (hh : h ≠ 0) (f : Coefficients) {p q : ℕ}
    (hp : 0 < p) (hd : DegreeBound f (p + q)) :
    (jumpCoefficient h (q + 1) f).coeff (p - 1) =
      f (p, q) * ((p : ℝ) * growth q) - f (q, p) * (p : ℝ) := by
  classical
  simp only [jumpCoefficient, Finsupp.linearCombination_apply, Finsupp.sum,
    finsetSum_coeff, coeff_smul, smul_eq_mul]
  calc
    _ = ∑ x ∈ f.support, f x *
        ((if x = (p, q) then (p : ℝ) * growth q else 0) -
          (if x = (q, p) then (p : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hb : x.1 + x.2 ≤ p + q := by
        apply le_of_not_gt
        intro hlt
        exact Finsupp.mem_support_iff.mp hx (hd x hlt)
      rw [jumpCoefficientBasis_top hh hp hb]
      simp only [Prod.ext_iff]
    _ = _ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, sum_select, sum_select]

lemma jumpCoefficient_eq_zero {h : ℝ} {f : Coefficients}
    (hz : ∀ z : ℝ, jump h z f = 0) (v : ℕ) : jumpCoefficient h v f = 0 := by
  apply Polynomial.funext
  intro z
  rw [← jump_coeff, hz z, coeff_zero, eval_zero]

theorem top_coefficient_relation {h : ℝ} (hh : h ≠ 0) {f : Coefficients} {p q : ℕ}
    (hp : 0 < p) (hd : DegreeBound f (p + q)) (hz : ∀ z : ℝ, jump h z f = 0) :
    f (q, p) = growth q * f (p, q) := by
  have he := congrArg (fun P : ℝ[X] => P.coeff (p - 1)) (jumpCoefficient_eq_zero hz (q + 1))
  rw [jumpCoefficient_top hh f hp hd, coeff_zero] at he
  have hn : (p : ℝ) ≠ 0 := by positivity
  have hf : (p : ℝ) * (f (q, p) - growth q * f (p, q)) = 0 := by
    linear_combination -he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hn)

end Rhone.Statistics.AtomicRank
