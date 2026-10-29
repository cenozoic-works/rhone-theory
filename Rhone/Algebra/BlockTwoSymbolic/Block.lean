/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.SymbolicFrequencies.Tower

/-! # Nonsingularity of the within-block systems over `ℚ(π_A, π_B)(u,v)(ρ)` -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

theorem linP3_ne_zero (c : GenericField.Fv SymbolicFrequencies.Kpi) :
    (C 3 * X + C c : Polynomial (GenericField.Fv SymbolicFrequencies.Kpi)) ≠ 0 := by
  intro hz
  have h1 := congrArg (fun p => Polynomial.coeff p 1) hz
  simp at h1

noncomputable def thAF : GenericField.Fuv SymbolicFrequencies.Kpi :=
    (GenericField.uu SymbolicFrequencies.Kpi + GenericField.vv SymbolicFrequencies.Kpi) / 2

noncomputable def thBF : GenericField.Fuv SymbolicFrequencies.Kpi :=
    (GenericField.uu SymbolicFrequencies.Kpi - GenericField.vv SymbolicFrequencies.Kpi) / 2

@[simp] theorem algebraMap_thAF :
    algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        thAF = GenericField.thA SymbolicFrequencies.Kpi := rfl

@[simp] theorem algebraMap_thBF :
    algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        thBF = GenericField.thB SymbolicFrequencies.Kpi := rfl

theorem uu_eq : GenericField.uu SymbolicFrequencies.Kpi = thAF + thBF := by rw [thAF, thBF]; ring

theorem vv_eq : GenericField.vv SymbolicFrequencies.Kpi = thAF - thBF := by rw [thAF, thBF]; ring

theorem algebraMap_P_C (x : GenericField.Fuv SymbolicFrequencies.Kpi) :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        (C x)
      = algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) x := RatFunc.algebraMap_C x

@[simp] theorem algebraMap_X_L :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi) X =
        GenericField.rhoL SymbolicFrequencies.Kpi := RatFunc.algebraMap_X

theorem polyL_ne_zero {p : GenericField.P SymbolicFrequencies.Kpi} (h : p ≠ 0) :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi) p ≠
        0 := _root_.Rhone.Algebra.algebraMap_ne_zero h

theorem constL_ne_zero {x : GenericField.Fuv SymbolicFrequencies.Kpi} (h : x ≠ 0) :
    algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        x ≠ 0 := by
  rw [← algebraMap_P_C]
  exact polyL_ne_zero fun hz => h (Polynomial.C_eq_zero.mp hz)

theorem linP_ne_zero {a b : GenericField.Fuv SymbolicFrequencies.Kpi} (h : a ≠ 0) :
    (C a * X + C b : GenericField.P SymbolicFrequencies.Kpi) ≠ 0 := by
  intro hz
  apply h
  have hc := congrArg (fun p => Polynomial.coeff p 1) hz
  simpa using hc

theorem quadP_ne_zero {a b c : GenericField.Fuv SymbolicFrequencies.Kpi} (h : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c : GenericField.P SymbolicFrequencies.Kpi) ≠ 0 := by
  intro hz
  apply h
  have hc := congrArg (fun p => Polynomial.coeff p 2) hz
  simpa using hc

theorem lin_ne_zero {a b : GenericField.Fuv SymbolicFrequencies.Kpi} (h : a ≠ 0) :
    algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        a * GenericField.rhoL SymbolicFrequencies.Kpi
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) b ≠ 0 := by
  have e : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) a * GenericField.rhoL SymbolicFrequencies.Kpi
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) b
      = algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
          (C a * X + C b) := by
    simp only [map_add, map_mul, algebraMap_P_C, algebraMap_X_L]
  rw [e]
  exact polyL_ne_zero (linP_ne_zero h)

theorem quad_ne_zero {a b c : GenericField.Fuv SymbolicFrequencies.Kpi} (h : a ≠ 0) :
    algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        a * GenericField.rhoL SymbolicFrequencies.Kpi ^ 2
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) b * GenericField.rhoL SymbolicFrequencies.Kpi
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) c ≠ 0 := by
  have e : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) a * GenericField.rhoL SymbolicFrequencies.Kpi ^ 2
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) b * GenericField.rhoL SymbolicFrequencies.Kpi
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) c
      = algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
          (C a * X ^ 2 + C b * X + C c) := by
    simp only [map_add, map_mul, map_pow, algebraMap_P_C, algebraMap_X_L]
  rw [e]
  exact polyL_ne_zero (quadP_ne_zero h)

theorem three_uu_add_ne_zero (c : GenericField.Fv SymbolicFrequencies.Kpi) :
    3 * GenericField.uu SymbolicFrequencies.Kpi + algebraMap
        (GenericField.Fv SymbolicFrequencies.Kpi) (GenericField.Fuv SymbolicFrequencies.Kpi) c ≠
        0 := by
  have h : algebraMap (Polynomial (GenericField.Fv SymbolicFrequencies.Kpi))
      (GenericField.Fuv SymbolicFrequencies.Kpi) (C 3 * X + C c)
      = 3 * GenericField.uu SymbolicFrequencies.Kpi + algebraMap
          (GenericField.Fv SymbolicFrequencies.Kpi) (GenericField.Fuv SymbolicFrequencies.Kpi) c :=
          by
    rw [map_add, map_mul, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
      map_ofNat]
    rfl
  rw [← h]
  exact _root_.Rhone.Algebra.algebraMap_ne_zero (linP3_ne_zero c)

theorem thAF_two_ne_zero : (2 + 2 * thAF : GenericField.Fuv SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : (2 + 2 * thAF : GenericField.Fuv SymbolicFrequencies.Kpi) = GenericField.uu
      SymbolicFrequencies.Kpi + GenericField.vv SymbolicFrequencies.Kpi + 2 := by
    rw [thAF]; ring
  rw [h]; exact SymbolicFrequencies.uu_add_vv_add_two_ne_zero SymbolicFrequencies.Kpi

theorem thBF_two_ne_zero : (2 + 2 * thBF : GenericField.Fuv SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : (2 + 2 * thBF : GenericField.Fuv SymbolicFrequencies.Kpi) = GenericField.uu
      SymbolicFrequencies.Kpi - GenericField.vv SymbolicFrequencies.Kpi + 2 := by
    rw [thBF]; ring
  rw [h]; exact SymbolicFrequencies.uu_sub_vv_add_two_ne_zero SymbolicFrequencies.Kpi

theorem thAF_thBF_two_ne_zero : (2 + thAF + thBF : GenericField.Fuv SymbolicFrequencies.Kpi) ≠ 0 :=
    by
  have h : (2 + thAF + thBF : GenericField.Fuv SymbolicFrequencies.Kpi) = GenericField.uu
      SymbolicFrequencies.Kpi + 2 := by
    rw [thAF, thBF]; ring
  rw [h]; exact GenericField.uu_add_two_ne_zero SymbolicFrequencies.Kpi

theorem thAF_two_thBF_ne_zero : (thAF + 2 * thBF + 2 : GenericField.Fuv SymbolicFrequencies.Kpi) ≠
    0 := by
  have hv : algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
      (GenericField.Fuv SymbolicFrequencies.Kpi) (4 - RatFunc.X)
      = 4 - GenericField.vv SymbolicFrequencies.Kpi := by rw [map_sub, map_ofNat]; rfl
  have h : (thAF + 2 * thBF + 2 : GenericField.Fuv SymbolicFrequencies.Kpi)
      = (3 * GenericField.uu SymbolicFrequencies.Kpi + algebraMap
          (GenericField.Fv SymbolicFrequencies.Kpi) (GenericField.Fuv SymbolicFrequencies.Kpi)
          (4 - RatFunc.X)) / 2 := by
    rw [hv, thAF, thBF]; ring
  rw [h]
  exact div_ne_zero (three_uu_add_ne_zero _) (by norm_num)

theorem two_thAF_thBF_ne_zero : (2 * thAF + thBF + 2 : GenericField.Fuv SymbolicFrequencies.Kpi) ≠
    0 := by
  have hv : algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
      (GenericField.Fuv SymbolicFrequencies.Kpi) (4 + RatFunc.X)
      = 4 + GenericField.vv SymbolicFrequencies.Kpi := by rw [map_add, map_ofNat]; rfl
  have h : (2 * thAF + thBF + 2 : GenericField.Fuv SymbolicFrequencies.Kpi)
      = (3 * GenericField.uu SymbolicFrequencies.Kpi + algebraMap
          (GenericField.Fv SymbolicFrequencies.Kpi) (GenericField.Fuv SymbolicFrequencies.Kpi)
          (4 + RatFunc.X)) / 2 := by
    rw [hv, thAF, thBF]; ring
  rw [h]
  exact div_ne_zero (three_uu_add_ne_zero _) (by norm_num)

section Blocks

local notation "tA" => GenericField.thA SymbolicFrequencies.Kpi
local notation "tB" => GenericField.thB SymbolicFrequencies.Kpi
local notation "r" => GenericField.rhoL SymbolicFrequencies.Kpi

theorem ne_lhs02 : (2 + 2 * tB : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (2 + 2 * thBF) = 2 + 2 * tB := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thBF]
  rw [← h]
  exact constL_ne_zero thBF_two_ne_zero

theorem ne_lhs20 : (2 + 2 * tA : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (2 + 2 * thAF) = 2 + 2 * tA := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thAF]
  rw [← h]
  exact constL_ne_zero thAF_two_ne_zero

theorem ne_lhs11 : (2 + tA + tB : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (2 + thAF + thBF) = 2 + tA + tB := by
    simp only [map_add, map_ofNat, algebraMap_thAF, algebraMap_thBF]
  rw [← h]
  exact constL_ne_zero thAF_thBF_two_ne_zero

theorem ne_d1_12 : (2 + tA + 2 * tB + r : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) 1 * r
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) (2 + thAF + 2 * thBF)
      = 2 + tA + 2 * tB + r := by
    simp only [map_add, map_mul, map_one, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero one_ne_zero

theorem ne_d1_21 : (2 + 2 * tA + tB + r : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) 1 * r
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) (2 + 2 * thAF + thBF)
      = 2 + 2 * tA + tB + r := by
    simp only [map_add, map_mul, map_one, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero one_ne_zero

theorem ne_E12 :
    ((6 + tA + 2 * tB) * (2 + tA + 2 * tB + r) - 4 * r : GenericField.L SymbolicFrequencies.Kpi) ≠
    0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (thAF + 2 * thBF + 2) * r
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi)
          ((thAF + 2 * thBF + 2) * (thAF + 2 * thBF + 6))
      = (6 + tA + 2 * tB) * (2 + tA + 2 * tB + r) - 4 * r := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero thAF_two_thBF_ne_zero

theorem ne_E21 :
    ((6 + 2 * tA + tB) * (2 + 2 * tA + tB + r) - 4 * r : GenericField.L SymbolicFrequencies.Kpi) ≠
    0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (2 * thAF + thBF + 2) * r
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi)
          ((2 * thAF + thBF + 2) * (2 * thAF + thBF + 6))
      = (6 + 2 * tA + tB) * (2 + 2 * tA + tB + r) - 4 * r := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero two_thAF_thBF_ne_zero

theorem ne_d2_22 : (2 + 2 * tA + 2 * tB + 2 * r : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) 2 * r
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) (2 + 2 * thAF + 2 * thBF)
      = 2 + 2 * tA + 2 * tB + 2 * r := by
    simp only [map_add, map_mul, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero two_ne_zero

theorem ne_d1_22 : (6 + 2 * tA + 2 * tB + r : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) 1 * r
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) (6 + 2 * thAF + 2 * thBF)
      = 6 + 2 * tA + 2 * tB + r := by
    simp only [map_add, map_mul, map_one, map_ofNat, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact lin_ne_zero one_ne_zero

theorem ne_W22 :
    ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) : GenericField.L
        SymbolicFrequencies.Kpi) ≠ 0 :=
  mul_ne_zero ne_d1_22 ne_d2_22

theorem ne_W4_22 :
    ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r : GenericField.L
        SymbolicFrequencies.Kpi) ≠ 0 := by
  have h : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) 2 * r ^ 2
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) (2 * (3 * thAF + 3 * thBF + 5)) * r
      + algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) (4 * (thAF + thBF + 1) * (thAF + thBF + 3))
      = (6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r := by
    simp only [map_add, map_mul, map_ofNat, map_one, algebraMap_thAF, algebraMap_thBF]
    ring
  rw [← h]
  exact quad_ne_zero two_ne_zero

theorem D22_eq :
    ((12 + 2 * tA + 2 * tB)
        * ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r)
      - 8 * r * (2 + 2 * tA + 2 * tB + 2 * r) : GenericField.L SymbolicFrequencies.Kpi)
      = algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
          (4 * GenericField.E22 SymbolicFrequencies.Kpi) := by
  have hu : algebraMap (GenericField.Fuv SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (GenericField.uu SymbolicFrequencies.Kpi) = tA +
      tB := by
    rw [uu_eq, map_add, algebraMap_thAF, algebraMap_thBF]
  rw [GenericField.E22, GenericField.E22a, GenericField.E22b, GenericField.E22c]
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one, algebraMap_P_C, algebraMap_X_L, hu]
  ring

theorem ne_D22 :
    ((12 + 2 * tA + 2 * tB)
        * ((6 + 2 * tA + 2 * tB + r) * (2 + 2 * tA + 2 * tB + 2 * r) - 4 * r)
      - 8 * r * (2 + 2 * tA + 2 * tB + 2 * r) : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  rw [D22_eq]
  exact polyL_ne_zero (mul_ne_zero (by norm_num) (GenericField.E22_ne_zero SymbolicFrequencies.Kpi))

end Blocks

end Rhone.Algebra.BlockTwoSymbolic
