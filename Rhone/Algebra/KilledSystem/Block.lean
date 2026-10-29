/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Solve
public import Rhone.Algebra.E22

/-! # Nonsingularity of the within-block systems -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

open Polynomial

@[simp] theorem algebraMap_thAF : algebraMap Fuv L thAF = thA := rfl
@[simp] theorem algebraMap_thBF : algebraMap Fuv L thBF = thB := rfl
@[simp] theorem algebraMap_X_L : algebraMap P L X = rhoL := RatFunc.algebraMap_X

@[simp] theorem algebraMap_uu : algebraMap Fuv L uu = thA + thB := by
  rw [uu_eq, map_add]; rfl

theorem polyL_ne_zero {p : P} (h : p ≠ 0) : algebraMap P L p ≠ 0 := algebraMap_ne_zero h

theorem constL_ne_zero {x : Fuv} (h : x ≠ 0) : algebraMap Fuv L x ≠ 0 := by
  rw [← algebraMap_P_C]
  exact polyL_ne_zero fun hz => h (Polynomial.C_eq_zero.mp hz)

theorem linP_ne_zero {a b : Fuv} (h : a ≠ 0) : (C a * X + C b : P) ≠ 0 := by
  intro hz
  apply h
  have hc := congrArg (fun p => Polynomial.coeff p 1) hz
  simpa using hc

theorem quadP_ne_zero {a b c : Fuv} (h : a ≠ 0) : (C a * X ^ 2 + C b * X + C c : P) ≠ 0 := by
  intro hz
  apply h
  have hc := congrArg (fun p => Polynomial.coeff p 2) hz
  simpa using hc

theorem lin_ne_zero {a b : Fuv} (h : a ≠ 0) :
    algebraMap Fuv L a * rhoL + algebraMap Fuv L b ≠ 0 := by
  have e : algebraMap Fuv L a * rhoL + algebraMap Fuv L b = algebraMap P L (C a * X + C b) := by
    simp only [map_add, map_mul, algebraMap_P_C, algebraMap_X_L]
  rw [e]
  exact polyL_ne_zero (linP_ne_zero h)

theorem quad_ne_zero {a b c : Fuv} (h : a ≠ 0) :
    algebraMap Fuv L a * rhoL ^ 2 + algebraMap Fuv L b * rhoL + algebraMap Fuv L c ≠ 0 := by
  have e : algebraMap Fuv L a * rhoL ^ 2 + algebraMap Fuv L b * rhoL + algebraMap Fuv L c
      = algebraMap P L (C a * X ^ 2 + C b * X + C c) := by
    simp only [map_add, map_mul, map_pow, algebraMap_P_C, algebraMap_X_L]
  rw [e]
  exact polyL_ne_zero (quadP_ne_zero h)

theorem three_uu_add_ne_zero (c : Fv) : 3 * uu + algebraMap Fv Fuv c ≠ 0 := by
  have h : 3 * uu + algebraMap Fv Fuv c = 3 * (uu + algebraMap Fv Fuv (c / 3)) := by
    rw [map_div₀, map_ofNat]; ring
  rw [h]
  exact mul_ne_zero (by norm_num) (uu_add_ne_zero _)

theorem thAF_two_ne_zero : (2 + 2 * thAF : Fuv) ≠ 0 := by
  have h : (2 + 2 * thAF : Fuv) = uu + vv + 2 := by rw [thAF]; ring
  rw [h]; exact uu_add_vv_add_two_ne_zero

theorem thBF_two_ne_zero : (2 + 2 * thBF : Fuv) ≠ 0 := by
  have h : (2 + 2 * thBF : Fuv) = uu - vv + 2 := by rw [thBF]; ring
  rw [h]; exact uu_sub_vv_add_two_ne_zero

theorem thAF_thBF_two_ne_zero : (2 + thAF + thBF : Fuv) ≠ 0 := by
  have h : (2 + thAF + thBF : Fuv) = uu + 2 := by rw [thAF, thBF]; ring
  rw [h]; exact uu_add_two_ne_zero

theorem thAF_two_thBF_ne_zero : (thAF + 2 * thBF + 2 : Fuv) ≠ 0 := by
  have hv : algebraMap Fv Fuv (4 - RatFunc.X) = 4 - vv := by rw [map_sub, map_ofNat]; rfl
  have h : (thAF + 2 * thBF + 2 : Fuv) = (3 * uu + algebraMap Fv Fuv (4 - RatFunc.X)) / 2 := by
    rw [hv, thAF, thBF]; ring
  rw [h]
  exact div_ne_zero (three_uu_add_ne_zero _) (by norm_num)

theorem two_thAF_thBF_ne_zero : (2 * thAF + thBF + 2 : Fuv) ≠ 0 := by
  have hv : algebraMap Fv Fuv (4 + RatFunc.X) = 4 + vv := by rw [map_add, map_ofNat]; rfl
  have h : (2 * thAF + thBF + 2 : Fuv) = (3 * uu + algebraMap Fv Fuv (4 + RatFunc.X)) / 2 := by
    rw [hv, thAF, thBF]; ring
  rw [h]
  exact div_ne_zero (three_uu_add_ne_zero _) (by norm_num)

theorem ne_lhs02 : (2 + 2 * thB : L) ≠ 0 := by
  have h : algebraMap Fuv L (2 + 2 * thBF) = 2 + 2 * thB := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thBF]
  rw [← h]
  exact constL_ne_zero thBF_two_ne_zero

theorem ne_lhs20 : (2 + 2 * thA : L) ≠ 0 := by
  have h : algebraMap Fuv L (2 + 2 * thAF) = 2 + 2 * thA := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thAF]
  rw [← h]
  exact constL_ne_zero thAF_two_ne_zero

theorem ne_lhs11 : (2 + thA + thB : L) ≠ 0 := by
  have h : algebraMap Fuv L (2 + thAF + thBF) = 2 + thA + thB := by
    simp only [map_add, map_ofNat, algebraMap_thAF, algebraMap_thBF]
  rw [← h]
  exact constL_ne_zero thAF_thBF_two_ne_zero

theorem ne_d1_12 : (2 + thA + 2 * thB + rhoL : L) ≠ 0 := by
  have h : algebraMap Fuv L 1 * rhoL + algebraMap Fuv L (2 + thAF + 2 * thBF)
      = 2 + thA + 2 * thB + rhoL := by
    simp only [map_add, map_mul, map_one, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero one_ne_zero

theorem ne_d1_21 : (2 + 2 * thA + thB + rhoL : L) ≠ 0 := by
  have h : algebraMap Fuv L 1 * rhoL + algebraMap Fuv L (2 + 2 * thAF + thBF)
      = 2 + 2 * thA + thB + rhoL := by
    simp only [map_add, map_mul, map_one, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero one_ne_zero

theorem ne_E12 :
    ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL : L) ≠ 0 := by
  have h : algebraMap Fuv L (thAF + 2 * thBF + 2) * rhoL
      + algebraMap Fuv L ((thAF + 2 * thBF + 2) * (thAF + 2 * thBF + 6))
      = (6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero thAF_two_thBF_ne_zero

theorem ne_E21 :
    ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL : L) ≠ 0 := by
  have h : algebraMap Fuv L (2 * thAF + thBF + 2) * rhoL
      + algebraMap Fuv L ((2 * thAF + thBF + 2) * (2 * thAF + thBF + 6))
      = (6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero two_thAF_thBF_ne_zero

theorem ne_d2_22 : (2 + 2 * thA + 2 * thB + 2 * rhoL : L) ≠ 0 := by
  have h : algebraMap Fuv L 2 * rhoL + algebraMap Fuv L (2 + 2 * thAF + 2 * thBF)
      = 2 + 2 * thA + 2 * thB + 2 * rhoL := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero two_ne_zero

theorem ne_d1_22 : (6 + 2 * thA + 2 * thB + rhoL : L) ≠ 0 := by
  have h : algebraMap Fuv L 1 * rhoL + algebraMap Fuv L (6 + 2 * thAF + 2 * thBF)
      = 6 + 2 * thA + 2 * thB + rhoL := by
    simp only [map_add, map_mul, map_one, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero one_ne_zero

theorem ne_W22 :
    ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) : L) ≠ 0 :=
  mul_ne_zero ne_d1_22 ne_d2_22

theorem ne_W4_22 :
    ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL : L)
      ≠ 0 := by
  have h : algebraMap Fuv L 2 * rhoL ^ 2
      + algebraMap Fuv L (2 * (3 * thAF + 3 * thBF + 5)) * rhoL
      + algebraMap Fuv L (4 * (thAF + thBF + 1) * (thAF + thBF + 3))
      = (6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL := by
    simp only [map_add, map_mul, map_ofNat, map_one, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact quad_ne_zero two_ne_zero

theorem D22_eq_T22_det :
    ((12 + 2 * thA + 2 * thB)
        * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL)
      - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL) : L) = algebraMap P L T22.det := by
  rw [T22_det, E22, E22a, E22b, E22c]
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one, algebraMap_P_C, algebraMap_X_L,
    algebraMap_uu]
  ring

theorem ne_D22 :
    ((12 + 2 * thA + 2 * thB)
        * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL)
      - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL) : L) ≠ 0 := by
  rw [D22_eq_T22_det]
  exact polyL_ne_zero T22_det_ne_zero

theorem eq_zero_of_mul {A x : L} (hA : A ≠ 0) (h : A * x = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hA
  · exact h'

end Rhone.Algebra.KilledSystem
