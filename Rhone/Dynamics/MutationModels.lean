/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Finite parent-independent redraw mutation on alleles

Source: ewens2004, sec. 12.2.3, eq. (12.14), pp. 375–376. -/

@[expose] public section
namespace Rhone.Dynamics.MutationModels
open Finset
variable {A : Type*} [Fintype A] [DecidableEq A]

def pimTransition (u : ℝ) (π : A → ℝ) (i j : A) : ℝ :=
  (1-u)*(if i=j then 1 else 0)+u*π j

/-- Source: ewens2004, eq. (12.14), p. 376. -/
theorem pim_stationary (u : ℝ) (π : A → ℝ) (hπ : ∑ i, π i = 1) (j : A) :
    ∑ i, π i*pimTransition u π i j = π j := by
  simp only [pimTransition, mul_add, sum_add_distrib]
  have hdiag : ∑ i, π i*((1-u)*(if i=j then 1 else 0)) = π j*(1-u) := by
    simp [mul_ite]
  rw [hdiag]
  simp only [← sum_mul, hπ, one_mul]
  ring

omit [Fintype A] in
/--
Source: ewens2004, eq. (12.14), p. 376, sec. 12.1.1, eq. (12.1)–(12.2), p. 372, eq. (2.164), p. 91.
-/
theorem pim_detailed_balance_general (u : ℝ) (π : A → ℝ) (i j : A) :
    π i*pimTransition u π i j = π j*pimTransition u π j i := by
  by_cases h : i=j
  · subst j; rfl
  · simp only [pimTransition, h, Ne.symm h, ite_false, mul_zero, zero_add]
    ring

/-- Source: ewens2004, eq. (12.14), p. 376. -/
theorem pim_markov (u : ℝ) (π : A → ℝ) (hπ0 : ∀ i, 0 ≤ π i)
    (hπ : ∑ i, π i = 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∀ i j, 0 ≤ pimTransition u π i j) ∧ (∀ i, ∑ j, pimTransition u π i j = 1) := by
  constructor
  · intro i j
    unfold pimTransition
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) (by positivity))
      (mul_nonneg hu0 (hπ0 j))
  · intro i
    simp [pimTransition, sum_add_distrib, ← mul_sum, hπ]

end Rhone.Dynamics.MutationModels
