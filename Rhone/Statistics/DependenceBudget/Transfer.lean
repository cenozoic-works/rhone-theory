/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic

/-! # Finite whole-data transfer bounds; not historical bytes -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.DependenceBudget

structure Law (X : Type*) [Fintype X] where
  mass : X → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

variable {X : Type*} [Fintype X]

noncomputable def rejection (P : Law X) (φ : X → ℝ) : ℝ :=
  ∑ x, P.mass x * φ x

noncomputable def totalVariation (P Q : Law X) : ℝ :=
  (∑ x, |P.mass x - Q.mass x|) / 2

theorem rejection_difference_le (P Q : Law X) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    |rejection P φ - rejection Q φ| ≤ totalVariation P Q := by
  have heq : rejection P φ - rejection Q φ =
      ∑ x, (P.mass x - Q.mass x) * (φ x - 1 / 2) := by
    simp only [rejection, mul_sub, sub_mul, Finset.sum_sub_distrib,
      ← Finset.sum_mul, P.total, Q.total]
    ring1
  rw [heq]
  calc
    |∑ x, (P.mass x - Q.mass x) * (φ x - 1 / 2)| ≤
        ∑ x, |(P.mass x - Q.mass x) * (φ x - 1 / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |P.mass x - Q.mass x| * (1 / 2) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply abs_le.mpr
      constructor <;> have hx := hφ x <;> linarith
    _ = totalVariation P Q := by rw [← Finset.sum_mul]; simp [totalVariation, div_eq_mul_inv]

theorem size_transfer (P Q : Law X) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α ε : ℝ}
    (hsize : rejection Q φ ≤ α) (hTV : totalVariation P Q ≤ ε) :
    rejection P φ ≤ α + ε := by
  have h := (abs_le.mp ((rejection_difference_le P Q φ hφ).trans hTV)).2
  linarith

theorem power_transfer (P Q : Law X) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {β ε : ℝ}
    (hpower : 1 - β ≤ rejection Q φ) (hTV : totalVariation P Q ≤ ε) :
    1 - β - ε ≤ rejection P φ := by
  have h := (abs_le.mp ((rejection_difference_le P Q φ hφ).trans hTV)).1
  linarith

structure Coupling (P Q : Law X) where
  mass : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ mass x y
  first : ∀ x, ∑ y, mass x y = P.mass x
  second : ∀ y, ∑ x, mass x y = Q.mass y

noncomputable def mismatch [DecidableEq X] {P Q : Law X} (R : Coupling P Q) : ℝ :=
  ∑ x, ∑ y, if x = y then 0 else R.mass x y

theorem coupling_difference_le [DecidableEq X] {P Q : Law X}
    (R : Coupling P Q) (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    |rejection P φ - rejection Q φ| ≤ mismatch R := by
  have hfirst : rejection P φ = ∑ x, ∑ y, R.mass x y * φ x := by
    simp only [← Finset.sum_mul, R.first, rejection]
  have hsecond : rejection Q φ = ∑ x, ∑ y, R.mass x y * φ y := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, R.second, rejection]
  rw [hfirst, hsecond, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    |∑ x, ∑ y, R.mass x y * (φ x - φ y)| ≤
        ∑ x, |∑ y, R.mass x y * (φ x - φ y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ mismatch R := by
      apply Finset.sum_le_sum
      intro x _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro y _
      by_cases hxy : x = y
      · subst y; simp
      · simp only [ite_eq_right hxy, abs_mul, abs_of_nonneg (R.nonneg x y)]
        have hb : |φ x - φ y| ≤ 1 := by
          apply abs_le.mpr
          constructor <;> have hx := hφ x <;> have hy := hφ y <;> linarith
        simpa using mul_le_mul_of_nonneg_left hb (R.nonneg x y)

theorem coupling_transfer [DecidableEq X] {P Q : Law X}
    (R : Coupling P Q) (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {ε : ℝ} (hbudget : mismatch R ≤ ε) :
    |rejection P φ - rejection Q φ| ≤ ε :=
  (coupling_difference_le R φ hφ).trans hbudget

end Rhone.Statistics.DependenceBudget
