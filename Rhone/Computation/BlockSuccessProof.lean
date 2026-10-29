/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.BackwardContinuantProof
public import Rhone.LinearAlgebra.ExplicitFormula.Pos
public import Mathlib.Algebra.Order.Ring.Rat

/-! # Error freedom of the executable block solver -/

@[expose] public section

namespace Rhone.Computation

theorem blockDet_positive (p : Params) (i j : Nat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hij : 0 < i + j) :
    0 < (forwardContinuants (blockDiagonal p i j) (blockBeta p i j)
      (min i j + 1)).getD (min i j + 2) 0 := by
  rw [forwardContinuants_det]
  exact Rhone.LinearAlgebra.ExplicitFormula.E_pos_all hθA hθB hρ hij

theorem solveBlock_eq_ok (p : Params) (i j : Nat) (rhs : Array Rat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hij : 0 < i + j) :
    solveBlock p i j rhs = .ok (applyBlockInverse p i j
      (forwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j + 1))
      (backwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j))
      (1 / Rhone.LinearAlgebra.Tridiag.E Rat i j p.thetaA p.thetaB p.rho) rhs) := by
  have hE := (Rhone.LinearAlgebra.ExplicitFormula.E_pos_all hθA hθB hρ hij).ne'
  simp only [solveBlock, forwardContinuants_det, backwardContinuants_det]
  simp [hE]
  rfl

end Rhone.Computation
