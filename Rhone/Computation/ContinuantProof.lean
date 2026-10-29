/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ContinuantArrayProof
public import Rhone.LinearAlgebra.Tridiag.Defs
import Mathlib.Tactic.Ring

/-! # Executable coefficients and the tridiagonal specification -/

@[expose] public section

namespace Rhone.Computation

private theorem rat_mul_pred (n : Nat) :
    (n : Rat) * ((n : Rat) - 1) = ((n * (n - 1) : Nat) : Rat) := by
  cases n with
  | zero => simp
  | succ n => push_cast; ring

theorem blockDiagonal_eq_dcoef (p : Params) (i j s : Nat) :
    blockDiagonal p i j s =
      Rhone.LinearAlgebra.Tridiag.dcoef Rat i j p.thetaA p.thetaB p.rho s := by
  simp only [blockDiagonal, Rhone.LinearAlgebra.Tridiag.dcoef, rat_mul_pred]
  ring

theorem blockBeta_zero (p : Params) (i j : Nat) : blockBeta p i j 0 = 0 := by
  simp [blockBeta]

theorem blockBeta_succ (p : Params) (i j s : Nat) (hi : s ≤ i) (hj : s ≤ j) :
    blockBeta p i j (s + 1) =
      Rhone.LinearAlgebra.Tridiag.bcoef Rat i j s *
        Rhone.LinearAlgebra.Tridiag.ccoef Rat p.rho s := by
  rw [Rhone.LinearAlgebra.Tridiag.bcoef_mul_ccoef]
  simp only [blockBeta, Nat.cast_mul, Nat.cast_sub hi, Nat.cast_sub hj,
    Nat.cast_add, Nat.cast_one]
  ring

theorem forwardContinuants_eq_cont (p : Params) (i j n r : Nat)
    (hn : n ≤ min i j + 1) (hr : r ≤ n) :
    (forwardContinuants (blockDiagonal p i j) (blockBeta p i j) n).getD (r + 1) 0 =
      Rhone.LinearAlgebra.Tridiag.cont
        (Rhone.LinearAlgebra.Tridiag.dcoef Rat i j p.thetaA p.thetaB p.rho)
        (Rhone.LinearAlgebra.Tridiag.bcoef Rat i j)
        (Rhone.LinearAlgebra.Tridiag.ccoef Rat p.rho) r := by
  apply forwardContinuants_getD
  · rfl
  · intro s hs
    cases s with
    | zero =>
      simp [Rhone.LinearAlgebra.Tridiag.cont, blockDiagonal_eq_dcoef]
    | succ s =>
      have hi : s ≤ i := by have := min_le_left i j; omega
      have hj : s ≤ j := by have := min_le_right i j; omega
      simp [Rhone.LinearAlgebra.Tridiag.cont, blockDiagonal_eq_dcoef,
        blockBeta_succ p i j s hi hj]
  · exact hr

theorem forwardContinuants_det (p : Params) (i j : Nat) :
    (forwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j + 1)).getD
        (min i j + 2) 0 =
      Rhone.LinearAlgebra.Tridiag.E Rat i j p.thetaA p.thetaB p.rho := by
  rw [Rhone.LinearAlgebra.Tridiag.E_eq_cont]
  exact forwardContinuants_eq_cont p i j (min i j + 1) (min i j + 1) le_rfl le_rfl

end Rhone.Computation
