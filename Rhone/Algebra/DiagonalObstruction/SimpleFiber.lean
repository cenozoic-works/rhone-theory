/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic

/-! # The `ρ = 0` fibre of the tridiagonal determinant: linear factors, simple marked root -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

open Polynomial

noncomputable def zeroFiber (m : ℕ) : ℚ[X] :=
  Rhone.LinearAlgebra.Tridiag.E ℚ[X] m m X 0 0

def markedPoint (m : ℕ) : ℚ := -2 * (2 * (m : ℚ) - 1)

noncomputable def fiberFactor (m t : ℕ) : ℚ[X] :=
  C (((2 * (m : ℚ) - t) * (2 * (m : ℚ) - t - 1))) + X * C (m : ℚ)

theorem zeroFiber_eq_prod {m : ℕ} (hm : 1 ≤ m) :
    zeroFiber m = ∏ t : Fin (m + 1), fiberFactor m t := by
  rw [zeroFiber, Rhone.LinearAlgebra.Tridiag.E_rho_zero, Nat.min_self]
  apply Finset.prod_congr rfl
  intro t _
  have ht : (t : ℕ) ≤ m := by omega
  have hsub : (t : ℕ) ≤ m + m := by omega
  have hsub1 : 1 ≤ m + m - (t : ℕ) := by omega
  simp only [Rhone.LinearAlgebra.Tridiag.dcoef, zero_mul, add_zero, fiberFactor]
  push_cast [Nat.cast_sub hsub, Nat.cast_sub hsub1]
  simp only [map_mul, map_sub, map_natCast, map_ofNat, map_one]
  ring

theorem eval_fiberFactor_marked (m t : ℕ) :
    (fiberFactor m t).eval (markedPoint m) =
      -(t : ℚ) * (4 * (m : ℚ) - t - 1) := by
  simp only [fiberFactor, markedPoint, eval_add, eval_C, eval_mul, eval_X]
  ring

theorem zeroFiber_marked_eq_zero {m : ℕ} (hm : 1 ≤ m) :
    (zeroFiber m).eval (markedPoint m) = 0 := by
  rw [zeroFiber_eq_prod hm, Fin.prod_univ_succ]
  simp [eval_fiberFactor_marked]

theorem zeroFiber_derivative_marked {m : ℕ} (hm : 1 ≤ m) :
    (zeroFiber m).derivative.eval (markedPoint m) =
      (m : ℚ) * ∏ t : Fin m,
        (-((t : ℕ) + 1 : ℚ) * (4 * (m : ℚ) - ((t : ℕ) + 1) - 1)) := by
  rw [zeroFiber_eq_prod hm, Fin.prod_univ_succ, derivative_mul]
  simp only [eval_add, eval_mul, eval_fiberFactor_marked, Fin.val_zero, Nat.cast_zero,
    neg_zero, zero_mul, add_zero]
  simp only [fiberFactor, derivative_add, derivative_C, zero_add, derivative_mul,
    derivative_X, one_mul, mul_zero, add_zero, eval_C]
  congr 1
  rw [eval_prod]
  apply Finset.prod_congr rfl
  intro t _
  simpa only [fiberFactor, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
    eval_fiberFactor_marked m t.succ

theorem zeroFiber_derivative_marked_ne_zero {m : ℕ} (hm : 1 ≤ m) :
    (zeroFiber m).derivative.eval (markedPoint m) ≠ 0 := by
  rw [zeroFiber_derivative_marked hm]
  apply mul_ne_zero
  · exact_mod_cast (by omega : m ≠ 0)
  · apply Finset.prod_ne_zero_iff.mpr
    intro t _
    have ht : (t : ℕ) < m := t.isLt
    have htq : (t : ℚ) < (m : ℚ) := by exact_mod_cast ht
    have hmq : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    apply mul_ne_zero
    · have : (0 : ℚ) < (t : ℕ) + 1 := by positivity
      exact neg_ne_zero.mpr this.ne'
    · exact (by linarith : (0 : ℚ) < 4 * (m : ℚ) - ((t : ℕ) + 1) - 1).ne'

end Rhone.Algebra.DiagonalObstruction
