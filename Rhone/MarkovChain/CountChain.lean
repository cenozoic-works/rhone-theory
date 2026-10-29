/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-! # Finite chains on counts -/

@[expose] public section

namespace Rhone.MarkovChain

abbrev CountKernel (N : ℕ) : Type := Fin (N + 1) → Fin (N + 1) → ℝ

namespace CountKernel

variable {N : ℕ}

def IsStochastic (P : CountKernel N) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

def expect (P : CountKernel N) (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ :=
  ∑ j, P i j * f j

def expectIter (P : CountKernel N) : ℕ → (Fin (N + 1) → ℝ) → Fin (N + 1) → ℝ
  | 0, f => f
  | t + 1, f => P.expect (P.expectIter t f)

def IsHarmonic (P : CountKernel N) (h : Fin (N + 1) → ℝ) : Prop :=
  ∀ i, P.expect h i = h i

theorem expect_const_mul (P : CountKernel N) (c : ℝ) (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    P.expect (fun j => c * f j) i = c * P.expect f i := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem expect_sub (P : CountKernel N) (f g : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    P.expect (fun j => f j - g j) i = P.expect f i - P.expect g i := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_const (P : CountKernel N) (hP : ∀ i, ∑ j, P i j = 1) (c : ℝ)
    (i : Fin (N + 1)) : P.expect (fun _ => c) i = c := by
  simp [expect, ← Finset.sum_mul, hP]

theorem expectIter_eigen (P : CountKernel N) (c : ℝ) (f : Fin (N + 1) → ℝ)
    (hf : ∀ i, P.expect f i = c * f i) (t : ℕ) (i : Fin (N + 1)) :
    P.expectIter t f i = c ^ t * f i := by
  induction t generalizing i with
  | zero => simp [expectIter]
  | succ t ih =>
    have : P.expectIter t f = fun j => c ^ t * f j := funext ih
    simp only [expectIter, this, expect_const_mul, hf]
    ring

end CountKernel

end Rhone.MarkovChain
