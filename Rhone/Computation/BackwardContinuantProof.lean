/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ContinuantProof
public import Rhone.Computation.BackwardArrayProof
public import Rhone.LinearAlgebra.RecombinationExpansion.Usmani

/-! # Backward arrays and trailing principal minors -/

@[expose] public section

namespace Rhone.Computation

theorem backwardContinuants_eq_Qc (p : Params) (i j r : Nat) (hr : r ≤ min i j + 2) :
    (backwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j)).getD r 0 =
      Rhone.LinearAlgebra.RecombinationExpansion.Qc
        (Rhone.LinearAlgebra.Tridiag.dcoef Rat i j p.thetaA p.thetaB p.rho)
        (Rhone.LinearAlgebra.Tridiag.bcoef Rat i j)
        (Rhone.LinearAlgebra.Tridiag.ccoef Rat p.rho) (min i j + 1) r := by
  apply backwardContinuants_getD
  · exact Rhone.LinearAlgebra.RecombinationExpansion.Qc_self _ _ _ _
  · simp
  · intro s hs
    have hi : s ≤ i := le_trans hs (min_le_left _ _)
    have hj : s ≤ j := le_trans hs (min_le_right _ _)
    rw [blockDiagonal_eq_dcoef, blockBeta_succ p i j s hi hj]
    exact Rhone.LinearAlgebra.RecombinationExpansion.Qc_rec _ _ _ (by omega)
  · exact hr

theorem backwardContinuants_det (p : Params) (i j : Nat) :
    (backwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j)).getD 0 0 =
      Rhone.LinearAlgebra.Tridiag.E Rat i j p.thetaA p.thetaB p.rho := by
  rw [backwardContinuants_eq_Qc p i j 0 (by omega),
    Rhone.LinearAlgebra.RecombinationExpansion.Qc_of_le _ _ _ (Nat.zero_le _), Nat.sub_zero,
    Rhone.LinearAlgebra.Tridiag.tridFrom_zero]
  rfl

theorem continuants_agree (p : Params) (i j : Nat) :
    (forwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j + 1)).getD
        (min i j + 2) 0 =
      (backwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j)).getD 0 0 := by
  rw [forwardContinuants_det, backwardContinuants_det]

end Rhone.Computation
