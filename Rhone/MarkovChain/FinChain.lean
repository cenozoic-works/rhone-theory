/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Finite-state Markov chains in discrete time -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset Matrix

structure FinChain (S : Type*) [Fintype S] where
  P : Matrix S S ℝ
  nonneg : ∀ x y, 0 ≤ P x y
  row_sum : ∀ x, ∑ y, P x y = 1

namespace FinChain

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

theorem mem_rowStochastic : C.P ∈ rowStochastic ℝ S :=
  mem_rowStochastic_iff_sum.2 ⟨C.nonneg, C.row_sum⟩

def ofRowStochastic (M : Matrix S S ℝ) (hM : M ∈ rowStochastic ℝ S) : FinChain S where
  P := M
  nonneg := (mem_rowStochastic_iff_sum.1 hM).1
  row_sum := (mem_rowStochastic_iff_sum.1 hM).2

def stepN (n : ℕ) : Matrix S S ℝ := C.P ^ n

def expect (f : S → ℝ) : S → ℝ := C.P *ᵥ f

def expectN (n : ℕ) (f : S → ℝ) : S → ℝ := C.stepN n *ᵥ f

def IsHarmonic (h : S → ℝ) : Prop := C.expect h = h

theorem stepN_zero : C.stepN 0 = 1 := pow_zero _

theorem stepN_one : C.stepN 1 = C.P := pow_one _

theorem stepN_succ (n : ℕ) : C.stepN (n + 1) = C.P * C.stepN n := pow_succ' _ _

theorem stepN_succ' (n : ℕ) : C.stepN (n + 1) = C.stepN n * C.P := pow_succ _ _

theorem stepN_add (m n : ℕ) : C.stepN (m + n) = C.stepN m * C.stepN n := pow_add _ _ _

theorem stepN_add_apply (m n : ℕ) (x y : S) :
    C.stepN (m + n) x y = ∑ z, C.stepN m x z * C.stepN n z y := by
  rw [stepN_add, Matrix.mul_apply]

theorem stepN_mem_rowStochastic (n : ℕ) : C.stepN n ∈ rowStochastic ℝ S :=
  pow_mem C.mem_rowStochastic n

theorem stepN_nonneg (n : ℕ) (x y : S) : 0 ≤ C.stepN n x y :=
  (mem_rowStochastic_iff_sum.1 (C.stepN_mem_rowStochastic n)).1 x y

theorem stepN_row_sum (n : ℕ) (x : S) : ∑ y, C.stepN n x y = 1 :=
  (mem_rowStochastic_iff_sum.1 (C.stepN_mem_rowStochastic n)).2 x

theorem stepN_le_one (n : ℕ) (x y : S) : C.stepN n x y ≤ 1 :=
  le_one_of_mem_rowStochastic (C.stepN_mem_rowStochastic n)

def iterate (n : ℕ) : FinChain S := ofRowStochastic (C.stepN n) (C.stepN_mem_rowStochastic n)

omit [DecidableEq S] in
theorem expect_apply (f : S → ℝ) (x : S) : C.expect f x = ∑ y, C.P x y * f y := rfl

theorem expectN_apply (n : ℕ) (f : S → ℝ) (x : S) :
    C.expectN n f x = ∑ y, C.stepN n x y * f y := rfl

@[simp] theorem expectN_zero (f : S → ℝ) : C.expectN 0 f = f := by
  simp [expectN, stepN_zero]

theorem expectN_one (f : S → ℝ) : C.expectN 1 f = C.expect f := by
  simp [expectN, expect, stepN_one]

theorem expectN_succ (n : ℕ) (f : S → ℝ) : C.expectN (n + 1) f = C.expect (C.expectN n f) := by
  simp [expectN, expect, stepN_succ, mulVec_mulVec]

theorem expectN_succ' (n : ℕ) (f : S → ℝ) : C.expectN (n + 1) f = C.expectN n (C.expect f) := by
  simp [expectN, expect, stepN_succ', mulVec_mulVec]

theorem expectN_add (m n : ℕ) (f : S → ℝ) :
    C.expectN (m + n) f = C.expectN m (C.expectN n f) := by
  simp [expectN, stepN_add, mulVec_mulVec]

theorem expectN_const (n : ℕ) (c : ℝ) : C.expectN n (fun _ => c) = fun _ => c := by
  funext x
  simp [expectN_apply, ← Finset.sum_mul, C.stepN_row_sum]

omit [DecidableEq S] in
theorem expect_const (c : ℝ) : C.expect (fun _ => c) = fun _ => c := by
  funext x
  simp [expect_apply, ← Finset.sum_mul, C.row_sum]

theorem expectN_add_fun (n : ℕ) (f g : S → ℝ) :
    C.expectN n (f + g) = C.expectN n f + C.expectN n g := mulVec_add _ _ _

theorem expectN_sub_fun (n : ℕ) (f g : S → ℝ) :
    C.expectN n (f - g) = C.expectN n f - C.expectN n g := mulVec_sub _ _ _

theorem expectN_smul (n : ℕ) (c : ℝ) (f : S → ℝ) :
    C.expectN n (c • f) = c • C.expectN n f := mulVec_smul _ _ _

omit [DecidableEq S] in
theorem expect_sub_fun (f g : S → ℝ) : C.expect (f - g) = C.expect f - C.expect g :=
  mulVec_sub _ _ _

theorem expectN_mono (n : ℕ) {f g : S → ℝ} (hfg : ∀ y, f y ≤ g y) (x : S) :
    C.expectN n f x ≤ C.expectN n g x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hfg y) (C.stepN_nonneg n x y)

theorem expectN_nonneg (n : ℕ) {f : S → ℝ} (hf : ∀ y, 0 ≤ f y) (x : S) : 0 ≤ C.expectN n f x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (C.stepN_nonneg n x y) (hf y)

theorem abs_expectN_le (n : ℕ) {f : S → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) (x : S) :
    |C.expectN n f x| ≤ M := by
  have h1 := C.expectN_mono n (fun y => (abs_le.1 (hf y)).2) x
  have h2 := C.expectN_mono n (fun y => (abs_le.1 (hf y)).1) x
  have hc := congrFun (C.expectN_const n M) x
  have hc' := congrFun (C.expectN_const n (-M)) x
  exact abs_le.2 ⟨by linarith, by linarith⟩

omit [DecidableEq S] in
theorem isHarmonic_iff (h : S → ℝ) : C.IsHarmonic h ↔ ∀ x, ∑ y, C.P x y * h y = h x :=
  funext_iff

omit [DecidableEq S] in
theorem isHarmonic_const (c : ℝ) : C.IsHarmonic fun _ => c := C.expect_const c

variable {C}

theorem IsHarmonic.expectN_eq {h : S → ℝ} (hh : C.IsHarmonic h) (n : ℕ) : C.expectN n h = h := by
  induction n with
  | zero => simp
  | succ n ih => rw [expectN_succ', hh, ih]

omit [DecidableEq S] in
theorem IsHarmonic.sub {g h : S → ℝ} (hg : C.IsHarmonic g) (hh : C.IsHarmonic h) :
    C.IsHarmonic (g - h) := by
  unfold IsHarmonic at *
  rw [expect_sub_fun, hg, hh]

end FinChain

end Rhone.MarkovChain
