/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Rhone.Algebra.E22

/-! # Consistency of the general `T^{(i,j)}` with the concrete `T^{(2,2)}` -/

@[expose] public section

namespace Rhone.Algebra.Tridiag

open Polynomial

noncomputable def thAP : P := C ((uu + vv) / 2)

noncomputable def thBP : P := C ((uu - vv) / 2)

theorem thAP_mul_two_add_thBP_mul_two : thAP * 2 + thBP * 2 = C (2 * uu) := by
  have h : thAP + thBP = C uu := by
    rw [thAP, thBP, ← map_add]
    congr 1
    ring
  rw [map_mul, map_ofNat]
  linear_combination 2 * h

theorem T_two_two : LinearAlgebra.Tridiag.T P 2 2 thAP thBP X = Rhone.Algebra.T22 := by
  have h := thAP_mul_two_add_thBP_mul_two
  rw [LinearAlgebra.Tridiag.T_two_two_generic, Rhone.Algebra.T22,
    show (12 : P) + thAP * 2 + thBP * 2 = C (2 * uu) + 12 from by linear_combination h,
    show (6 : P) + thAP * 2 + thBP * 2 + X = C (2 * uu) + 6 + X from by linear_combination h,
    show (2 : P) + thAP * 2 + thBP * 2 + X * 2 = C (2 * uu) + 2 + 2 * X from by
      linear_combination h,
    show -(X * 2) = -2 * X from by ring]

theorem E_two_two : LinearAlgebra.Tridiag.E P 2 2 thAP thBP X = 4 * Rhone.Algebra.E22 := by
  rw [LinearAlgebra.Tridiag.E, T_two_two, Rhone.Algebra.T22_det]

theorem algebraMap_thAP : algebraMap P L thAP = Rhone.Algebra.thA := by
  rw [thAP, RatFunc.algebraMap_C]; rfl

theorem algebraMap_thBP : algebraMap P L thBP = Rhone.Algebra.thB := by
  rw [thBP, RatFunc.algebraMap_C]; rfl

theorem E_two_two_L :
    LinearAlgebra.Tridiag.E L 2 2 Rhone.Algebra.thA Rhone.Algebra.thB Rhone.Algebra.rhoL = 4 *
        algebraMap P L Rhone.Algebra.E22 := by
  have h := LinearAlgebra.Tridiag.E_map (algebraMap P L : P →+* L) 2 2 thAP thBP X
  rw [algebraMap_thAP, algebraMap_thBP, RatFunc.algebraMap_X] at h
  rw [Rhone.Algebra.rhoL, ← h, E_two_two, map_mul, map_ofNat]

end Rhone.Algebra.Tridiag
