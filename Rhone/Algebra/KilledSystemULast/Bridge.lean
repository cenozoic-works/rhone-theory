/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystemULast.Recursion
public import Rhone.Algebra.GenericField.Swap
public import Rhone.Algebra.KilledSystem.NoFormula

/-! # The two readings solve the same system -/

@[expose] public section

set_option maxSynthPendingDepth 3

namespace Rhone.Algebra.KilledSystemULast

open Polynomial

open KilledSystem

theorem swapL_thAu : GenericField.swapL thAu = thA := by
  rw [thAu, GenericField.swapL_algebraMap]
  simp only [map_mul, map_add, GenericField.swapP_C, GenericField.swapP_X, GenericField.swapC_vv,
      map_inv₀, map_ofNat]
  rw [thA, map_div₀, map_add, map_ofNat, GenericField.uL, GenericField.vL]
  ring

theorem swapL_thBu : GenericField.swapL thBu = thB := by
  rw [thBu, GenericField.swapL_algebraMap]
  simp only [map_mul, map_sub, GenericField.swapP_C, GenericField.swapP_X, GenericField.swapC_vv,
      map_inv₀, map_ofNat]
  rw [thB, map_div₀, map_sub, map_ofNat, GenericField.uL, GenericField.vL]
  ring

theorem swapL_rhoU : GenericField.swapL rhoU = rhoL := by
  have h : rhoU = algebraMap P L (C rhoM) := (algebraMap_P_C rhoM).symm
  rw [h, GenericField.swapL_algebraMap, GenericField.swapP_C]
  exact GenericField.swapC_uu

theorem swapL_piA0 : GenericField.swapL piA0 = piA0 := by
  rw [piA0, map_div₀, map_one, map_ofNat]

theorem swapL_piA1 : GenericField.swapL piA1 = piA1 := by
  rw [piA1, map_div₀, map_ofNat, map_ofNat]

theorem swapL_piB0 : GenericField.swapL piB0 = piB0 := by
  rw [piB0, map_div₀, map_ofNat, map_ofNat]

theorem swapL_piB1 : GenericField.swapL piB1 = piB1 := by
  rw [piB1, map_div₀, map_ofNat, map_ofNat]

theorem isSolution_swapL {q : St → L} (hq : IsSolutionU q) :
    IsSolution (fun s => GenericField.swapL (q s)) := by
  constructor
  · intro s hs
    have h := congrArg GenericField.swapL (hq.1 s hs)
    rw [map_mul, lhsC_map, rhsC_map] at h
    simp only [swapL_thAu, swapL_thBu, swapL_rhoU, swapL_piA0, swapL_piA1, swapL_piB0,
      swapL_piB1, map_mul, map_one] at h
    exact h
  · intro s hs
    have h := congrArg GenericField.swapL (hq.2 s hs)
    rw [bdryC_map] at h
    simp only [swapL_piA0, swapL_piA1, swapL_piB0, swapL_piB1] at h
    exact h

theorem eq_q22u_of_isSolutionU_swap {q : St → L} (hq : IsSolutionU q) : q s22 = q22u := by
  apply GenericField.swapL_injective
  rw [GenericField.swapL_q22u]
  exact eq_q22_of_isSolution (isSolution_swapL hq)

end Rhone.Algebra.KilledSystemULast
