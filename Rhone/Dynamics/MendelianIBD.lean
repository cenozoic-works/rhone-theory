/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring
/-!
# Mendelian identity by descent from founder-copy labels

Source: wright1931, p. 107. -/
@[expose] public section
namespace Rhone.Dynamics.MendelianIBD
open Finset
private def founderMatch {A : Type*} [DecidableEq A] (a b : A) : ℝ :=
  if a = b then 1 else 0
private theorem founderMatch_eq {A : Type*} [DecidableEq A] (a b : A) :
    founderMatch a b = if a = b then 1 else 0 := rfl
private theorem founderMatch_self {A : Type*} [DecidableEq A] (a : A) :
    founderMatch a a = 1 := by simp [founderMatch]
private theorem founderMatch_comm {A : Type*} [DecidableEq A] (a b : A) :
    founderMatch a b = founderMatch b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp [founderMatch, h, Ne.symm h]
def mendelianChild {A : Type*} (X Y : Fin 2 → A) (i j : Fin 2) : Fin 2 → A :=
  ![X i, Y j]
noncomputable def founderIbd {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X : O → Fin 2 → A) : ℝ :=
  ∑ o, w o * (if X o 0 = X o 1 then 1 else 0)
noncomputable def founderKinship {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) : ℝ :=
  ∑ o, w o * ∑ i : Fin 2, ∑ j : Fin 2, (if X o i = Y o j then 1 else 0) / 4
noncomputable def selfedIbd {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X : O → Fin 2 → A) : ℝ :=
  ∑ o, ∑ i : Fin 2, ∑ j : Fin 2, w o / 4 *
    (if mendelianChild (X o) (X o) i j 0 = mendelianChild (X o) (X o) i j 1
      then 1 else 0)
noncomputable def siblingKinship {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) : ℝ :=
  ∑ o, ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
    w o / 16 * founderKinship (fun _ : Unit => 1)
      (fun _ => mendelianChild (X o) (Y o) i j)
      (fun _ => mendelianChild (X o) (Y o) k l)
/-- Source: wright1931, p. 107. -/
theorem selfed_ibd_eq
    {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X : O → Fin 2 → A)
    (hw0 : ∀ o, 0 ≤ w o) (hw : Finset.sum Finset.univ w = 1) :
    selfedIbd w X = (1 + founderIbd w X)/2 := by
  have hpoint : ∀ o, (∑ i : Fin 2, ∑ j : Fin 2, w o / 4 *
      (if mendelianChild (X o) (X o) i j 0 = mendelianChild (X o) (X o) i j 1
        then 1 else 0)) = w o * (1 + (if X o 0 = X o 1 then 1 else 0))/2 := by
    intro o
    by_cases h : X o 0 = X o 1
    · simp [Fin.sum_univ_two, mendelianChild, h, eq_comm]
      ring
    · simp [Fin.sum_univ_two, mendelianChild, h, eq_comm]
      ring
  unfold selfedIbd founderIbd
  simp_rw [hpoint]
  have hn : 0 ≤ ∑ o, w o := sum_nonneg fun o _ => hw0 o
  simp only [mul_add, mul_one, ← sum_div, sum_add_distrib, hw]
/-- Source: wright1931, p. 107. -/
theorem sibling_kinship_eq
    {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A)
    (hw0 : ∀ o, 0 ≤ w o) (hw : Finset.sum Finset.univ w = 1) :
    siblingKinship w X Y =
      (2 + founderIbd w X + founderIbd w Y + 4 * founderKinship w X Y)/8 := by
  have hpoint : ∀ o,
      (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
        w o / 16 * founderKinship (fun _ : Unit => 1)
          (fun _ => mendelianChild (X o) (Y o) i j)
          (fun _ => mendelianChild (X o) (Y o) k l)) =
      w o * (2 + (if X o 0 = X o 1 then 1 else 0) +
        (if Y o 0 = Y o 1 then 1 else 0) +
        ∑ i : Fin 2, ∑ j : Fin 2, (if X o i = Y o j then 1 else 0))/8 := by
    intro o
    simp only [founderKinship, Fin.sum_univ_two, Fintype.sum_unique, one_mul]
    dsimp +instances only [mendelianChild, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [← founderMatch_eq,
      founderMatch_comm (X o 1) (X o 0),
      founderMatch_comm (Y o 1) (Y o 0),
      founderMatch_comm (Y o 0) (X o 0),
      founderMatch_comm (Y o 0) (X o 1),
      founderMatch_comm (Y o 1) (X o 0),
      founderMatch_comm (Y o 1) (X o 1)]
    simp only [ite_true]
    ring
  unfold siblingKinship
  simp_rw [hpoint]
  unfold founderIbd founderKinship
  have hn : 0 ≤ ∑ o, w o := sum_nonneg fun o _ => hw0 o
  simp only [mul_add, ← mul_div_assoc, ← sum_div, sum_add_distrib, ← sum_mul, hw]
  ring
end Rhone.Dynamics.MendelianIBD
