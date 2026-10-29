/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! # Finite-alphabet score algebra for the stationary three-tip channel -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator

def pairScore (K : ℕ) (a b : Fin K) : ℝ :=
  ((K : ℝ)*(if a = b then 1 else 0) - 1)/(K - 1)

def tripleScore (K : ℕ) (a b c : Fin K) : ℝ :=
  ((K : ℝ)^2*(if a = b ∧ a = c then 1 else 0) -
    K*((if a = b then 1 else 0) + (if a = c then 1 else 0) +
      (if b = c then 1 else 0)) + 2)/((K - 1)*(K - 2))

def patternMass (K : ℕ) (x y z : ℝ) (a b c : Fin K) : ℝ :=
  (1 - x - 2*y + 2*z)/(K : ℝ)^3 +
    (x - z)*(if a = b then 1 else 0)/(K : ℝ)^2 +
    (y - z)*((if a = c then 1 else 0) + (if b = c then 1 else 0))/(K : ℝ)^2 +
    z*(if a = b ∧ a = c then 1 else 0)/K

lemma patternMass_pair_marginal {K : ℕ} (hK : 0 < K) (x y z : ℝ) (a b : Fin K) :
    (∑ c, patternMass K x y z a b c) =
      (1 - x)/(K : ℝ)^2 + x*(if a = b then 1 else 0)/K := by
  have hn : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  by_cases hab : a = b
  · subst b
    simp [patternMass, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    field_simp
    ring
  · simp [patternMass, hab, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    field_simp
    ring

lemma patternMass_noncherry_marginal {K : ℕ} (hK : 0 < K) (x y z : ℝ) (a c : Fin K) :
    (∑ b, patternMass K x y z a b c) =
      (1 - y)/(K : ℝ)^2 + y*(if a = c then 1 else 0)/K := by
  have hn : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  by_cases hac : a = c
  · subst c
    simp [patternMass, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, eq_comm]
    field_simp
    ring
  · simp [patternMass, hac, Finset.sum_add_distrib, ← Finset.sum_div]
    field_simp
    ring

lemma patternMass_swap (K : ℕ) (x y z : ℝ) (a b c : Fin K) :
    patternMass K x y z a b c = patternMass K x y z b a c := by
  have he : (a = b ∧ a = c) ↔ (b = a ∧ b = c) := by
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h.symm, h.symm.trans h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨h.symm, h.symm.trans h'⟩
  simp only [patternMass, he, eq_comm]
  ring

end Rhone.Statistics.ThreeSiteSeparator
