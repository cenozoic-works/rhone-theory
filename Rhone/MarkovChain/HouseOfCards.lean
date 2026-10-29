/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.MutationModels
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Tactic.FieldSimp

/-!
# A finite-effect quantitative house-of-cards mutation–selection law

Source: kingman1978_selection, eq. (4.12), p. 7, sec. 5, p. 8; turelli1984, eq. (3.1), p. 149;
barton_turelli1987, p. 161, eq. (3.8b). -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.HouseOfCards
open Finset
/--
Source: kingman1978_selection, p. 2; turelli1984, eq. (3.1), p. 149; barton_turelli1987, p. 161, eq.
(3.8b). -/
def redraw {A : Type*} (ν : A → ℝ) : Option A → ℝ
  | none => 0
  | some i => ν i

/-- Source: turelli1984, eq. (2.9), p. 142. -/
def fitness {A : Type*} (a : A → ℝ) (S : ℝ) : Option A → ℝ
  | none => 1
  | some i => Real.exp (-(a i)^2/(2*S))

/-- Source: kingman1978_selection, eq. (4.12), p. 7; barton_turelli1987, p. 161, eq. (3.8b). -/
noncomputable def optimumMass {A : Type*} [Fintype A]
    (ν a : A → ℝ) (S u : ℝ) : ℝ :=
  1-u*∑ i, ν i/(1-Real.exp (-(a i)^2/(2*S)))

/-- Source: kingman1978_selection, eq. (4.12), p. 7, sec. 5, p. 8; barton_turelli1987, p. 161, eq.
(3.8b). -/
noncomputable def equilibrium {A : Type*} [Fintype A]
    (ν a : A → ℝ) (S u : ℝ) : Option A → ℝ
  | none => optimumMass ν a S u
  | some i => u*ν i/(1-Real.exp (-(a i)^2/(2*S)))

/-- Source: kingman1978_selection, eq. (1.2)–(1.3), p. 2; turelli1984, eq. (3.1), p. 149;
barton_turelli1987, p. 161, eq. (3.8b). -/
noncomputable def mutationSelection {A : Type*} [Fintype A] [DecidableEq A]
    (ν a : A → ℝ) (S u : ℝ) (p : Option A → ℝ) (j : Option A) : ℝ :=
  ∑ i, p i*fitness a S i/(∑ k, p k*fitness a S k)*
    Rhone.Dynamics.MutationModels.pimTransition u (redraw ν) i j

/-- Source: kingman1978_selection, eq. (4.12), p. 7; barton_turelli1987, p. 161, eq. (3.8b). -/
theorem equilibrium_total {A : Type*} [Fintype A]
    (ν a : A → ℝ) (S u : ℝ) : ∑ i, equilibrium ν a S u i = 1 := by
  simp only [Fintype.sum_option, equilibrium, optimumMass, mul_div_assoc, ← mul_sum]
  ring

/-- Source: kingman1978_selection, eq. (4.11)–(4.12), p. 7; barton_turelli1987, p. 161, eq. (3.8b).
-/
theorem equilibrium_mean_fitness {A : Type*} [Fintype A]
    (ν a : A → ℝ) (S u : ℝ) (hν : ∑ i, ν i = 1)
    (hS : 0 < S) (ha : ∀ i, a i ≠ 0) :
    ∑ i, equilibrium ν a S u i*fitness a S i = 1-u := by
  have hd (i : A) : 1-Real.exp (-(a i)^2/(2*S)) ≠ 0 := by
    have hn : -(a i)^2/(2*S) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos
      (sq_pos_of_ne_zero (ha i))) (by positivity)
    have he : Real.exp (-(a i)^2/(2*S)) < 1 := Real.exp_lt_one_iff.mpr hn
    linarith
  have he (i : A) : u*ν i/(1-Real.exp (-(a i)^2/(2*S)))*
      Real.exp (-(a i)^2/(2*S)) =
      u*ν i/(1-Real.exp (-(a i)^2/(2*S)))-u*ν i := by
    have hdi := hd i
    generalize Real.exp (-(a i)^2/(2*S)) = e at hdi ⊢
    field_simp [hdi]
    ring
  simp only [Fintype.sum_option, equilibrium, fitness, mul_one, optimumMass]
  simp_rw [he]
  simp only [sum_sub_distrib, mul_div_assoc, ← mul_sum, hν, mul_one]
  ring

/--
Source: kingman1978_selection, eq. (4.1), (4.12), pp. 5, 7; barton_turelli1987, p. 161, eq. (3.8b).
-/
theorem equilibrium_nonneg {A : Type*} [Fintype A]
    (ν a : A → ℝ) (S u : ℝ) (hν0 : ∀ i, 0 ≤ ν i)
    (hS : 0 < S) (ha : ∀ i, a i ≠ 0) (hu : 0 ≤ u)
    (hmass : 0 ≤ optimumMass ν a S u) :
    ∀ i, 0 ≤ equilibrium ν a S u i := by
  intro i
  cases i with
  | none => exact hmass
  | some i =>
    have hn : -(a i)^2/(2*S) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos
      (sq_pos_of_ne_zero (ha i))) (by positivity)
    have he : Real.exp (-(a i)^2/(2*S)) < 1 := Real.exp_lt_one_iff.mpr hn
    exact div_nonneg (mul_nonneg hu (hν0 i)) (sub_nonneg.mpr he.le)

/-- Source: barton_turelli1987, p. 161, eq. (3.8b). -/
theorem equilibrium_stationary {A : Type*} [Fintype A] [DecidableEq A]
    (ν a : A → ℝ) (S u : ℝ) (hν : ∑ i, ν i = 1)
    (hS : 0 < S) (ha : ∀ i, a i ≠ 0) (hu : u < 1) :
    mutationSelection ν a S u (equilibrium ν a S u) = equilibrium ν a S u := by
  have hden : 1-u ≠ 0 := ne_of_gt (sub_pos.mpr hu)
  funext j
  unfold mutationSelection
  rw [equilibrium_mean_fitness ν a S u hν hS ha]
  simp only [Rhone.Dynamics.MutationModels.pimTransition, mul_add, sum_add_distrib]
  have hdiag : (∑ i, equilibrium ν a S u i*fitness a S i/(1-u)*
      ((1-u)*(if i=j then 1 else 0))) = equilibrium ν a S u j*fitness a S j := by
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
    field_simp
  rw [hdiag]
  have hsum : (∑ i, equilibrium ν a S u i*fitness a S i/(1-u)) = 1 := by
    rw [← sum_div, equilibrium_mean_fitness ν a S u hν hS ha]
    exact div_self hden
  rw [← sum_mul, hsum, one_mul]
  cases j with
  | none => simp [equilibrium, fitness, redraw]
  | some i =>
    have hn : -(a i)^2/(2*S) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos
      (sq_pos_of_ne_zero (ha i))) (by positivity)
    have hd : 1-Real.exp (-(a i)^2/(2*S)) ≠ 0 := by
      have he := Real.exp_lt_one_iff.mpr hn
      linarith
    simp only [equilibrium, fitness, redraw]
    generalize Real.exp (-(a i)^2/(2*S)) = e at hd ⊢
    field_simp [hd]
    ring

end Rhone.MarkovChain.HouseOfCards
