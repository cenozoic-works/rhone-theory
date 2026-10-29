/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystemULast.Solve

/-! # Nonsingularity of the within-block systems, `u`-last -/

@[expose] public section

namespace Rhone.Algebra.KilledSystemULast

open Polynomial

open KilledSystem

theorem ne_of_map_eq (k x : L) (p : P) (hp : p ≠ 0) (h : k * x = algebraMap P L p) : x ≠ 0 := by
  intro hx
  rw [hx, mul_zero] at h
  exact polyL_ne_zero hp h.symm

theorem linU_ne_zero {a b : Fuv} (ha : a ≠ 0) {p : P} (h : p = C a * X + C b) : p ≠ 0 := by
  rw [h]; exact linP_ne_zero ha

theorem quadU_ne_zero {a b c : Fuv} (ha : a ≠ 0) {p : P}
    (h : p = C a * X ^ 2 + C b * X + C c) : p ≠ 0 := by
  rw [h]; exact quadP_ne_zero ha

theorem neU_lhs02 : (2 + 2 * thBu : L) ≠ 0 := by
  refine ne_of_map_eq 1 _ (2 + tBU) ?_ ?_
  · exact linU_ne_zero (a := 1) (b := 2 - vv) one_ne_zero
      (by simp only [tBU, map_sub, map_ofNat, map_one]; ring)
  · simp only [map_add, map_ofNat, algebraMap_tBU]; ring

theorem neU_lhs20 : (2 + 2 * thAu : L) ≠ 0 := by
  refine ne_of_map_eq 1 _ (2 + tAU) ?_ ?_
  · exact linU_ne_zero (a := 1) (b := 2 + vv) one_ne_zero
      (by simp only [tAU, map_add, map_ofNat, map_one]; ring)
  · simp only [map_add, map_ofNat, algebraMap_tAU]; ring

theorem neU_lhs11 : (2 + thAu + thBu : L) ≠ 0 := by
  refine ne_of_map_eq 2 _ (4 + tAU + tBU) ?_ ?_
  · exact linU_ne_zero (a := 2) (b := 4) two_ne_zero
      (by simp only [tAU, tBU, map_ofNat]; ring)
  · simp only [map_add, map_ofNat, algebraMap_tAU, algebraMap_tBU]; ring

theorem neU_d1_12 : (2 + thAu + 2 * thBu + rhoU : L) ≠ 0 := by
  refine ne_of_map_eq 2 _ (4 + tAU + 2 * tBU + 2 * rhoPU) ?_ ?_
  · exact linU_ne_zero (a := 3) (b := 4 - vv + 2 * rhoM) (by norm_num)
      (by simp only [tAU, tBU, rhoPU, map_add, map_sub, map_mul, map_ofNat]; ring)
  · simp only [map_add, map_mul, map_ofNat, algebraMap_tAU, algebraMap_tBU, algebraMap_rhoPU]
    ring

theorem neU_d1_21 : (2 + 2 * thAu + thBu + rhoU : L) ≠ 0 := by
  refine ne_of_map_eq 2 _ (4 + 2 * tAU + tBU + 2 * rhoPU) ?_ ?_
  · exact linU_ne_zero (a := 3) (b := 4 + vv + 2 * rhoM) (by norm_num)
      (by simp only [tAU, tBU, rhoPU, map_add, map_mul, map_ofNat]; ring)
  · simp only [map_add, map_mul, map_ofNat, algebraMap_tAU, algebraMap_tBU, algebraMap_rhoPU]
    ring

theorem neU_E12 :
    ((6 + thAu + 2 * thBu) * (2 + thAu + 2 * thBu + rhoU) - 4 * rhoU : L) ≠ 0 := by
  refine ne_of_map_eq 4 _
    ((12 + tAU + 2 * tBU) * (4 + tAU + 2 * tBU + 2 * rhoPU) - 16 * rhoPU) ?_ ?_
  · exact quadU_ne_zero (a := 9) (b := 48 + 6 * rhoM - 6 * vv)
      (c := vv ^ 2 - 16 * vv - 2 * rhoM * vv + 48 + 8 * rhoM) (by norm_num)
      (by simp only [tAU, tBU, rhoPU, map_add, map_sub, map_mul, map_pow, map_ofNat]; ring)
  · simp only [map_sub, map_add, map_mul, map_ofNat, algebraMap_tAU, algebraMap_tBU,
      algebraMap_rhoPU]
    ring

theorem neU_E21 :
    ((6 + 2 * thAu + thBu) * (2 + 2 * thAu + thBu + rhoU) - 4 * rhoU : L) ≠ 0 := by
  refine ne_of_map_eq 4 _
    ((12 + 2 * tAU + tBU) * (4 + 2 * tAU + tBU + 2 * rhoPU) - 16 * rhoPU) ?_ ?_
  · exact quadU_ne_zero (a := 9) (b := 48 + 6 * rhoM + 6 * vv)
      (c := vv ^ 2 + 16 * vv + 2 * rhoM * vv + 48 + 8 * rhoM) (by norm_num)
      (by simp only [tAU, tBU, rhoPU, map_add, map_mul, map_pow, map_ofNat]; ring)
  · simp only [map_sub, map_add, map_mul, map_ofNat, algebraMap_tAU, algebraMap_tBU,
      algebraMap_rhoPU]
    ring

theorem neU_d2_22 : (2 + 2 * thAu + 2 * thBu + 2 * rhoU : L) ≠ 0 := by
  refine ne_of_map_eq 1 _ (2 + tAU + tBU + 2 * rhoPU) ?_ ?_
  · exact linU_ne_zero (a := 2) (b := 2 + 2 * rhoM) two_ne_zero
      (by simp only [tAU, tBU, rhoPU, map_add, map_mul, map_ofNat]; ring)
  · simp only [map_add, map_mul, map_ofNat, algebraMap_tAU, algebraMap_tBU, algebraMap_rhoPU]
    ring

theorem neU_d1_22 : (6 + 2 * thAu + 2 * thBu + rhoU : L) ≠ 0 := by
  refine ne_of_map_eq 1 _ (6 + tAU + tBU + rhoPU) ?_ ?_
  · exact linU_ne_zero (a := 2) (b := 6 + rhoM) two_ne_zero
      (by simp only [tAU, tBU, rhoPU, map_add, map_ofNat]; ring)
  · simp only [map_add, map_ofNat, algebraMap_tAU, algebraMap_tBU, algebraMap_rhoPU]
    ring

theorem neU_W22 :
    ((6 + 2 * thAu + 2 * thBu + rhoU) * (2 + 2 * thAu + 2 * thBu + 2 * rhoU) : L) ≠ 0 := by
  refine ne_of_map_eq 1 _ ((6 + tAU + tBU + rhoPU) * (2 + tAU + tBU + 2 * rhoPU)) ?_ ?_
  · exact quadU_ne_zero (a := 4) (b := 16 + 6 * rhoM) (c := 12 + 14 * rhoM + 2 * rhoM ^ 2)
      (by norm_num)
      (by simp only [tAU, tBU, rhoPU, map_add, map_mul, map_pow, map_ofNat]; ring)
  · simp only [map_add, map_mul, map_ofNat, algebraMap_tAU, algebraMap_tBU, algebraMap_rhoPU]
    ring

theorem neU_W4_22 :
    ((6 + 2 * thAu + 2 * thBu + rhoU) * (2 + 2 * thAu + 2 * thBu + 2 * rhoU) - 4 * rhoU : L)
      ≠ 0 := by
  refine ne_of_map_eq 1 _
    ((6 + tAU + tBU + rhoPU) * (2 + tAU + tBU + 2 * rhoPU) - 4 * rhoPU) ?_ ?_
  · exact quadU_ne_zero (a := 4) (b := 16 + 6 * rhoM) (c := 12 + 10 * rhoM + 2 * rhoM ^ 2)
      (by norm_num)
      (by simp only [tAU, tBU, rhoPU, map_add, map_mul, map_pow, map_ofNat]; ring)
  · simp only [map_sub, map_add, map_mul, map_ofNat, algebraMap_tAU, algebraMap_tBU,
      algebraMap_rhoPU]
    ring

theorem D22U_eq :
    (12 + tAU + tBU) * ((6 + tAU + tBU + rhoPU) * (2 + tAU + tBU + 2 * rhoPU) - 4 * rhoPU)
        - 8 * rhoPU * (2 + tAU + tBU + 2 * rhoPU)
      = 4 * E22u := by
  simp only [tAU, tBU, rhoPU, E22u, rhoM, map_add, map_mul, map_pow, map_ofNat]
  ring

theorem neU_D22 :
    ((12 + 2 * thAu + 2 * thBu)
        * ((6 + 2 * thAu + 2 * thBu + rhoU) * (2 + 2 * thAu + 2 * thBu + 2 * rhoU) - 4 * rhoU)
      - 8 * rhoU * (2 + 2 * thAu + 2 * thBu + 2 * rhoU) : L) ≠ 0 := by
  refine ne_of_map_eq 1 _ (4 * E22u) ?_ ?_
  · exact mul_ne_zero (by norm_num) E22u_ne_zero
  · rw [← D22U_eq]
    simp only [map_sub, map_add, map_mul, map_ofNat, algebraMap_tAU, algebraMap_tBU,
      algebraMap_rhoPU]
    ring

end Rhone.Algebra.KilledSystemULast
