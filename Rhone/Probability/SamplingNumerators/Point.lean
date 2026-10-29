/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Basic
public import Rhone.Probability.DiagonalChain.Small

/-! # Exact rational certificates at a smooth point of the top determinant -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators
open Matrix LinearAlgebra.Tridiag Analysis.RecombinationExpansion
    LinearAlgebra.RecombinationExpansion Analysis.DenominatorEquation DenominatorEquation
variable {S : Type*} [CommRing S]
private theorem point_usmani_three (d b c : ℕ → S) :
    Rhone.LinearAlgebra.RecombinationExpansion.usmani d b c 3 =
      !![d 1 * d 2 - b 1 * c 1, -b 0 * d 2, b 0 * b 1;
         -c 0 * d 2, d 0 * d 2, -b 1 * d 0;
         c 0 * c 1, -c 1 * d 0, d 0 * d 1 - b 0 * c 0] := by
  have q2 : Rhone.LinearAlgebra.RecombinationExpansion.Qc d b c 3 2 = d 2 := by
    rw [Rhone.LinearAlgebra.RecombinationExpansion.Qc_rec d b c (by omega : 2 < 3)]
    norm_num
  have q1 : Rhone.LinearAlgebra.RecombinationExpansion.Qc d b c 3 1 = d 1 * d 2 - b 1 * c 1 := by
    rw [Rhone.LinearAlgebra.RecombinationExpansion.Qc_rec d b c (by omega : 1 < 3), q2]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Rhone.LinearAlgebra.RecombinationExpansion.usmani_apply,
        Rhone.LinearAlgebra.RecombinationExpansion.usmaniEntry,
      Rhone.LinearAlgebra.RecombinationExpansion.runProd, Rhone.LinearAlgebra.Tridiag.cont, q1, q2,
      Finset.prod_Ico_succ_top, Finset.prod_range_succ]
  ring

private theorem E22_at_point : E ℚ 2 2 1 (-11) 0 = -2016 := by
  rw [E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, dcoef, bcoef, ccoef]

private theorem E23_at_point : E ℚ 2 3 1 (-11) 0 = -5225 := by
  rw [E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, dcoef, bcoef, ccoef]

private theorem E32_at_point : E ℚ 3 2 1 (-11) 0 = 91 := by
  rw [E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, dcoef, bcoef, ccoef]

private theorem n22_at_point : n22 (1 : ℚ) (-11) 0 = ![-2368, -1664, -4480] := by
  change (usmani (dcoef ℚ 2 2 1 (-11) 0) (bcoef ℚ 2 2) (ccoef ℚ 0) 3) *ᵥ
    s22 (1 : ℚ) (-11) = _
  rw [point_usmani_three]
  ext i
  fin_cases i <;> norm_num [dcoef, bcoef, ccoef, s22, c22, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

private theorem n23_at_point :
    n23 (1 : ℚ) (-11) 0 = ![42185088, 9985536, 48875904] := by
  change (usmani (dcoef ℚ 2 3 1 (-11) 0) (bcoef ℚ 2 3) (ccoef ℚ 0) 3) *ᵥ
    s23 (1 : ℚ) (-11) 0 = _
  rw [point_usmani_three]
  ext i
  fin_cases i <;> norm_num [dcoef, bcoef, ccoef, s23, E22_at_point, n22_at_point,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

private theorem n32_at_point :
    n32 (1 : ℚ) (-11) 0 = ![-1222272, -390144, -470400] := by
  change (usmani (dcoef ℚ 3 2 1 (-11) 0) (bcoef ℚ 3 2) (ccoef ℚ 0) 3) *ᵥ
    s32 (1 : ℚ) (-11) 0 = _
  rw [point_usmani_three]
  ext i
  fin_cases i <;> norm_num [dcoef, bcoef, ccoef, s32, E22_at_point, n22_at_point,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

private theorem U33_row_at_point :
    (U ℚ 3 3 1 (-11) 0) 0 = ![-4320, 7776, -3456, 288] := by
  have q2 : Qc (dcoef ℚ 3 3 1 (-11) 0) (bcoef ℚ 3 3) (ccoef ℚ 0) 4 3 = -24 := by
    rw [Qc_rec _ _ _ (by omega : 3 < 4)]
    norm_num [dcoef, bcoef, ccoef]
  have q1 : Qc (dcoef ℚ 3 3 1 (-11) 0) (bcoef ℚ 3 3) (ccoef ℚ 0) 4 2 = 432 := by
    rw [Qc_rec _ _ _ (by omega : 2 < 4), q2]
    norm_num [dcoef, bcoef, ccoef]
  have q0 : Qc (dcoef ℚ 3 3 1 (-11) 0) (bcoef ℚ 3 3) (ccoef ℚ 0) 4 1 = -4320 := by
    rw [Qc_rec _ _ _ (by omega : 1 < 4), q1]
    norm_num [dcoef, bcoef, ccoef]
  ext i
  fin_cases i <;> norm_num [U_apply, usmaniEntry, runProd, LinearAlgebra.Tridiag.cont,
    q0, q1, q2, Finset.prod_Ico_succ_top, Finset.prod_range_succ, bcoef]

theorem n33_at_point : n33 (1 : ℚ) (-11) 0 0 = 632126751252480 := by
  change (∑ j : Fin 4, U ℚ 3 3 1 (-11) 0 0 j * s33 (1 : ℚ) (-11) 0 j) = _
  rw [U33_row_at_point, Fin.sum_univ_four]
  norm_num [s33, E23_at_point, E32_at_point, n22_at_point, n23_at_point, n32_at_point,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem E33_at_point : E ℚ 3 3 1 (-11) 0 = 0 := by
  rw [E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, dcoef, bcoef, ccoef]

theorem d33_at_positive_point_ne_zero : d33 (1 : ℚ) 1 0 ≠ 0 := by
  norm_num [d33, c33, E_eq_cont, LinearAlgebra.Tridiag.cont, dcoef, bcoef, ccoef]

end Rhone.Probability.SamplingNumerators
