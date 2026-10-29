/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.E22u
public import Rhone.Algebra.BlockTwoSymbolic.Block

/-! # Nonsingularity of the within-block systems, `u`-last, over `ℚ(π_A, π_B)(v, ρ)(u)` -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

noncomputable def tAUπ : GenericField.P SymbolicFrequencies.Kpi := X + C
    (GenericField.vv SymbolicFrequencies.Kpi)

noncomputable def tBUπ : GenericField.P SymbolicFrequencies.Kpi := X - C
    (GenericField.vv SymbolicFrequencies.Kpi)

noncomputable def rhoPUπ : GenericField.P SymbolicFrequencies.Kpi := C rhoMπ

noncomputable def thAuπ : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
    (C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
        (X + C (GenericField.vv SymbolicFrequencies.Kpi)))

noncomputable def thBuπ : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
    (C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
        (X - C (GenericField.vv SymbolicFrequencies.Kpi)))

noncomputable def rhoUπ : GenericField.L SymbolicFrequencies.Kpi := algebraMap
    (GenericField.Fuv SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi) rhoMπ

theorem C_two_Pπ :
    (C (2 : GenericField.Fuv SymbolicFrequencies.Kpi) : GenericField.P SymbolicFrequencies.Kpi) =
    2 := map_ofNat Polynomial.C 2

theorem tAUπ_eq : tAUπ = 2 *
    (C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
    (X + C (GenericField.vv SymbolicFrequencies.Kpi))) := by
  rw [tAUπ, ← C_two_Pπ, ← mul_assoc, ← map_mul]
  norm_num

theorem tBUπ_eq : tBUπ = 2 *
    (C (2 : GenericField.Fuv SymbolicFrequencies.Kpi)⁻¹ *
    (X - C (GenericField.vv SymbolicFrequencies.Kpi))) := by
  rw [tBUπ, ← C_two_Pπ, ← mul_assoc, ← map_mul]
  norm_num

@[simp] theorem algebraMap_tAUπ :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        tAUπ = 2 * thAuπ := by
  rw [tAUπ_eq, map_mul, map_ofNat, thAuπ]

@[simp] theorem algebraMap_tBUπ :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        tBUπ = 2 * thBuπ := by
  rw [tBUπ_eq, map_mul, map_ofNat, thBuπ]

@[simp] theorem algebraMap_rhoPUπ :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        rhoPUπ = rhoUπ := RatFunc.algebraMap_C _

theorem ne_of_map_eq (k x : GenericField.L SymbolicFrequencies.Kpi)
    (p : GenericField.P SymbolicFrequencies.Kpi) (hp : p ≠ 0)
    (h : k * x = algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) p) : x ≠ 0 := by
  intro hx
  rw [hx, mul_zero] at h
  exact polyL_ne_zero hp h.symm

theorem linU_ne_zero {a b : GenericField.Fuv SymbolicFrequencies.Kpi} (ha : a ≠ 0)
    {p : GenericField.P SymbolicFrequencies.Kpi}
    (h : p = C a * X + C b) : p ≠ 0 := by
  rw [h]; exact linP_ne_zero ha

theorem quadU_ne_zero {a b c : GenericField.Fuv SymbolicFrequencies.Kpi} (ha : a ≠ 0)
    {p : GenericField.P SymbolicFrequencies.Kpi}
    (h : p = C a * X ^ 2 + C b * X + C c) : p ≠ 0 := by
  rw [h]; exact quadP_ne_zero ha

theorem neU_lhs02 : (2 + 2 * thBuπ : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  refine ne_of_map_eq 1 _ (2 + tBUπ) ?_ ?_
  · exact linU_ne_zero (a := 1) (b := 2 - GenericField.vv SymbolicFrequencies.Kpi) one_ne_zero
      (by simp only [tBUπ, map_sub, map_ofNat, map_one]; ring)
  · simp only [map_add, map_ofNat, algebraMap_tBUπ]; ring

theorem neU_lhs20 : (2 + 2 * thAuπ : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  refine ne_of_map_eq 1 _ (2 + tAUπ) ?_ ?_
  · exact linU_ne_zero (a := 1) (b := 2 + GenericField.vv SymbolicFrequencies.Kpi) one_ne_zero
      (by simp only [tAUπ, map_add, map_ofNat, map_one]; ring)
  · simp only [map_add, map_ofNat, algebraMap_tAUπ]; ring

theorem neU_lhs11 : (2 + thAuπ + thBuπ : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  refine ne_of_map_eq 2 _ (4 + tAUπ + tBUπ) ?_ ?_
  · exact linU_ne_zero (a := 2) (b := 4) two_ne_zero
      (by simp only [tAUπ, tBUπ, map_ofNat]; ring)
  · simp only [map_add, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ]; ring

theorem neU_d1_12 : (2 + thAuπ + 2 * thBuπ + rhoUπ : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 :=
    by
  refine ne_of_map_eq 2 _ (4 + tAUπ + 2 * tBUπ + 2 * rhoPUπ) ?_ ?_
  · exact linU_ne_zero (a := 3) (b := 4 - GenericField.vv SymbolicFrequencies.Kpi + 2 * rhoMπ)
      (by norm_num)
      (by simp only [tAUπ, tBUπ, rhoPUπ, map_add, map_sub, map_mul, map_ofNat]; ring)
  · simp only [map_add, map_mul, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ, algebraMap_rhoPUπ]
    ring

theorem neU_d1_21 : (2 + 2 * thAuπ + thBuπ + rhoUπ : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 :=
    by
  refine ne_of_map_eq 2 _ (4 + 2 * tAUπ + tBUπ + 2 * rhoPUπ) ?_ ?_
  · exact linU_ne_zero (a := 3) (b := 4 + GenericField.vv SymbolicFrequencies.Kpi + 2 * rhoMπ)
      (by norm_num)
      (by simp only [tAUπ, tBUπ, rhoPUπ, map_add, map_mul, map_ofNat]; ring)
  · simp only [map_add, map_mul, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ, algebraMap_rhoPUπ]
    ring

theorem neU_E12 :
    ((6 + thAuπ + 2 * thBuπ) * (2 + thAuπ + 2 * thBuπ + rhoUπ) - 4 * rhoUπ :
      GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  refine ne_of_map_eq 4 _
    ((12 + tAUπ + 2 * tBUπ) * (4 + tAUπ + 2 * tBUπ + 2 * rhoPUπ) - 16 * rhoPUπ) ?_ ?_
  · exact quadU_ne_zero (a := 9) (b := 48 + 6 * rhoMπ - 6 * GenericField.vv SymbolicFrequencies.Kpi)
      (c := GenericField.vv SymbolicFrequencies.Kpi ^ 2 - 16 * GenericField.vv
          SymbolicFrequencies.Kpi - 2 * rhoMπ * GenericField.vv SymbolicFrequencies.Kpi + 48 + 8 *
          rhoMπ)
      (by norm_num)
      (by simp only [tAUπ, tBUπ, rhoPUπ, map_add, map_sub, map_mul, map_pow, map_ofNat]; ring)
  · simp only [map_sub, map_add, map_mul, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ,
      algebraMap_rhoPUπ]
    ring

theorem neU_E21 :
    ((6 + 2 * thAuπ + thBuπ) * (2 + 2 * thAuπ + thBuπ + rhoUπ) - 4 * rhoUπ :
      GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  refine ne_of_map_eq 4 _
    ((12 + 2 * tAUπ + tBUπ) * (4 + 2 * tAUπ + tBUπ + 2 * rhoPUπ) - 16 * rhoPUπ) ?_ ?_
  · exact quadU_ne_zero (a := 9) (b := 48 + 6 * rhoMπ + 6 * GenericField.vv SymbolicFrequencies.Kpi)
      (c := GenericField.vv SymbolicFrequencies.Kpi ^ 2 + 16 * GenericField.vv
          SymbolicFrequencies.Kpi + 2 * rhoMπ * GenericField.vv SymbolicFrequencies.Kpi + 48 + 8 *
          rhoMπ)
      (by norm_num)
      (by simp only [tAUπ, tBUπ, rhoPUπ, map_add, map_mul, map_pow, map_ofNat]; ring)
  · simp only [map_sub, map_add, map_mul, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ,
      algebraMap_rhoPUπ]
    ring

theorem neU_d2_22 :
    (2 + 2 * thAuπ + 2 * thBuπ + 2 * rhoUπ : GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  refine ne_of_map_eq 1 _ (2 + tAUπ + tBUπ + 2 * rhoPUπ) ?_ ?_
  · exact linU_ne_zero (a := 2) (b := 2 + 2 * rhoMπ) two_ne_zero
      (by simp only [tAUπ, tBUπ, rhoPUπ, map_add, map_mul, map_ofNat]; ring)
  · simp only [map_add, map_mul, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ, algebraMap_rhoPUπ]
    ring

theorem neU_d1_22 : (6 + 2 * thAuπ + 2 * thBuπ + rhoUπ : GenericField.L SymbolicFrequencies.Kpi) ≠
    0 := by
  refine ne_of_map_eq 1 _ (6 + tAUπ + tBUπ + rhoPUπ) ?_ ?_
  · exact linU_ne_zero (a := 2) (b := 6 + rhoMπ) two_ne_zero
      (by simp only [tAUπ, tBUπ, rhoPUπ, map_add, map_ofNat]; ring)
  · simp only [map_add, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ, algebraMap_rhoPUπ]
    ring

theorem neU_W22 :
    ((6 + 2 * thAuπ + 2 * thBuπ + rhoUπ) * (2 + 2 * thAuπ + 2 * thBuπ + 2 * rhoUπ) :
      GenericField.L SymbolicFrequencies.Kpi) ≠ 0 :=
  mul_ne_zero neU_d1_22 neU_d2_22

theorem neU_W4_22 :
    ((6 + 2 * thAuπ + 2 * thBuπ + rhoUπ) * (2 + 2 * thAuπ + 2 * thBuπ + 2 * rhoUπ) - 4 * rhoUπ :
      GenericField.L SymbolicFrequencies.Kpi) ≠ 0 := by
  refine ne_of_map_eq 1 _
    ((6 + tAUπ + tBUπ + rhoPUπ) * (2 + tAUπ + tBUπ + 2 * rhoPUπ) - 4 * rhoPUπ) ?_ ?_
  · exact quadU_ne_zero (a := 4) (b := 16 + 6 * rhoMπ) (c := 12 + 10 * rhoMπ + 2 * rhoMπ ^ 2)
      (by norm_num)
      (by simp only [tAUπ, tBUπ, rhoPUπ, map_add, map_mul, map_pow, map_ofNat]; ring)
  · simp only [map_sub, map_add, map_mul, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ,
      algebraMap_rhoPUπ]
    ring

theorem D22Uπ_eq :
    (12 + tAUπ + tBUπ) * ((6 + tAUπ + tBUπ + rhoPUπ) * (2 + tAUπ + tBUπ + 2 * rhoPUπ)
        - 4 * rhoPUπ)
      - 8 * rhoPUπ * (2 + tAUπ + tBUπ + 2 * rhoPUπ)
      = 4 * E22uπ := by
  simp only [tAUπ, tBUπ, rhoPUπ, E22uπ, map_add, map_mul, map_pow, map_ofNat]
  ring

theorem neU_D22 :
    ((12 + 2 * thAuπ + 2 * thBuπ)
        * ((6 + 2 * thAuπ + 2 * thBuπ + rhoUπ) * (2 + 2 * thAuπ + 2 * thBuπ + 2 * rhoUπ)
          - 4 * rhoUπ)
      - 8 * rhoUπ * (2 + 2 * thAuπ + 2 * thBuπ + 2 * rhoUπ) : GenericField.L
          SymbolicFrequencies.Kpi) ≠ 0 := by
  refine ne_of_map_eq 1 _ (4 * E22uπ) ?_ ?_
  · exact mul_ne_zero (by norm_num) E22uπ_ne_zero
  · rw [← D22Uπ_eq]
    simp only [map_sub, map_add, map_mul, map_ofNat, algebraMap_tAUπ, algebraMap_tBUπ,
      algebraMap_rhoPUπ]
    ring

end Rhone.Algebra.BlockTwoSymbolic
