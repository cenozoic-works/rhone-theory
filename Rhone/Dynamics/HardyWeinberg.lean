/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Hardy–Weinberg in one generation

Source: hardy1908, p. 49; weinberg1908, p. 380; ewens2004, sec. 1.2. -/

@[expose] public section

namespace Rhone.Dynamics

open Finset

variable {K : ℕ}

noncomputable def alleleFreq (g : Fin K × Fin K → ℝ) (c : Fin K) : ℝ :=
  (1 / 2) * ∑ ab, g ab * ((if ab.1 = c then 1 else 0) + (if ab.2 = c then 1 else 0))

noncomputable def randomMating (g : Fin K × Fin K → ℝ) : Fin K × Fin K → ℝ :=
  fun cd => alleleFreq g cd.1 * alleleFreq g cd.2

theorem sum_alleleFreq (g : Fin K × Fin K → ℝ) (hg : ∑ ab, g ab = 1) :
    ∑ c, alleleFreq g c = 1 := by
  unfold alleleFreq
  rw [← Finset.mul_sum, Finset.sum_comm]
  have : ∀ ab : Fin K × Fin K, ∑ c, g ab * ((if ab.1 = c then 1 else 0)
      + (if ab.2 = c then 1 else 0)) = 2 * g ab := by
    intro ab
    simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    simp
    ring
  simp only [this, ← Finset.mul_sum, hg]
  norm_num

theorem sum_randomMating (g : Fin K × Fin K → ℝ) (hg : ∑ ab, g ab = 1) :
    ∑ cd, randomMating g cd = 1 := by
  unfold randomMating
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_alleleFreq g hg, one_mul]

theorem randomMating_nonneg (g : Fin K × Fin K → ℝ) (hg : ∀ ab, 0 ≤ g ab) (cd : Fin K × Fin K) :
    0 ≤ randomMating g cd := by
  have : ∀ c, 0 ≤ alleleFreq g c := fun c =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun ab _ => mul_nonneg (hg ab) (by positivity))
  exact mul_nonneg (this _) (this _)

private theorem alleleFreq_prod (p : Fin K → ℝ) (hp : ∑ c, p c = 1) (e : Fin K) :
    alleleFreq (fun cd => p cd.1 * p cd.2) e = p e := by
  unfold alleleFreq
  rw [Fintype.sum_prod_type]
  have : ∀ c d : Fin K, p c * p d * ((if c = e then (1 : ℝ) else 0) + (if d = e then 1 else 0)) =
      (if c = e then p e * p d else 0) + (if d = e then p c * p e else 0) := by
    intro c d
    by_cases hc : c = e <;> by_cases hd : d = e
    all_goals simp [hc, hd]
    ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_mul, hp]
  have h2 : ∀ x : Fin K, ∑ y : Fin K, (if x = e then p e * p y else 0) =
      if x = e then p e else 0 := by
    intro x
    split_ifs <;> simp [← Finset.mul_sum, hp]
  simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem alleleFreq_randomMating (g : Fin K × Fin K → ℝ) (hg : ∑ ab, g ab = 1) (e : Fin K) :
    alleleFreq (randomMating g) e = alleleFreq g e :=
  alleleFreq_prod (alleleFreq g) (sum_alleleFreq g hg) e

theorem randomMating_idempotent (g : Fin K × Fin K → ℝ) (hg : ∑ ab, g ab = 1) :
    randomMating (randomMating g) = randomMating g := by
  funext cd
  simp only [randomMating, alleleFreq_randomMating g hg]

theorem hw_two_allele (g : Fin 2 × Fin 2 → ℝ) (hg : ∑ ab, g ab = 1) (p : ℝ)
    (hp : p = g (0, 0) + (g (0, 1) + g (1, 0)) / 2) :
    alleleFreq g 0 = p ∧ alleleFreq g 1 = 1 - p ∧ randomMating g (0, 0) = p ^ 2 ∧
      randomMating g (0, 1) + randomMating g (1, 0) = 2 * p * (1 - p) ∧
      randomMating g (1, 1) = (1 - p) ^ 2 := by
  have h0 : alleleFreq g 0 = p := by
    rw [hp]
    simp [alleleFreq, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have h1 : alleleFreq g 1 = 1 - p := by
    have := sum_alleleFreq g hg
    rw [Fin.sum_univ_two, h0] at this
    linarith
  refine ⟨h0, h1, ?_, ?_, ?_⟩ <;> simp only [randomMating, h0, h1] <;> ring

theorem hw_fixed_iff (x y z : ℝ) (h : x + y + z = 1) :
    x = (x + y / 2) ^ 2 ↔ x * z = (y / 2) ^ 2 := by
  have hz : z = 1 - x - y := by linarith
  subst hz
  constructor <;> intro h' <;> nlinarith [h']

end Rhone.Dynamics
