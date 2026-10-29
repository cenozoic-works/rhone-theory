/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystemULast.Data
public import Rhone.Algebra.KilledSystem.Block

/-! # From a polynomial certificate to a solution of the `u`-last system -/

@[expose] public section

namespace Rhone.Algebra.KilledSystemULast

open Polynomial

open KilledSystem

theorem DcomU_eq :
    DcomU = C 225 * (C 1 * X + C (vv + 2)) * (C 1 * X + C (2 - vv)) * E22u := by
  simp only [DcomU, E22u, rhoM, map_add, map_sub, map_neg, map_mul, map_pow,
    map_ofNat, map_one]
  ring

theorem C_225_ne_zero : (C (225 : Fuv) : P) ≠ 0 := Polynomial.C_ne_zero.mpr (by norm_num)

theorem DcomU_ne_zero : DcomU ≠ 0 := by
  rw [DcomU_eq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero C_225_ne_zero (linP_ne_zero one_ne_zero))
    (linP_ne_zero one_ne_zero)) E22u_ne_zero

theorem DcomU_L_ne_zero : algebraMap P L DcomU ≠ 0 := algebraMap_ne_zero DcomU_ne_zero

theorem quint_smul (r a5 a4 a3 a2 a1 a0 b5 b4 b3 b2 b1 b0 : Fuv)
    (h5 : a5 = r * b5) (h4 : a4 = r * b4) (h3 : a3 = r * b3) (h2 : a2 = r * b2)
    (h1 : a1 = r * b1) (h0 : a0 = r * b0) :
    C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0
      = C r * (C b5 * X ^ 5 + C b4 * X ^ 4 + C b3 * X ^ 3 + C b2 * X ^ 2 + C b1 * X + C b0) := by
  subst h5; subst h4; subst h3; subst h2; subst h1; subst h0
  simp only [map_mul]
  ring

theorem rhsC_LU_scaled (F : St → L) (s : St) :
    rhsC 30 (5 * (2 * thAu)) (10 * (2 * thAu)) (6 * (2 * thBu)) (9 * (2 * thBu))
        (30 * rhoU) F s
      = 30 * rhsC 1 (thAu * piA0) (thAu * piA1) (thBu * piB0) (thBu * piB1) rhoU F s := by
  have h := rhsC_scale (30 : L) 1 (thAu * piA0) (thAu * piA1) (thBu * piB0) (thBu * piB1)
    rhoU F s
  rw [show ((30 : L) * 1) = 30 from by ring] at h
  rw [show ((30 : L) * (thAu * piA0)) = 5 * (2 * thAu) from by rw [piA0]; ring] at h
  rw [show ((30 : L) * (thAu * piA1)) = 10 * (2 * thAu) from by rw [piA1]; ring] at h
  rw [show ((30 : L) * (thBu * piB0)) = 6 * (2 * thBu) from by rw [piB0]; ring] at h
  rw [show ((30 : L) * (thBu * piB1)) = 9 * (2 * thBu) from by rw [piB1]; ring] at h
  exact h

theorem isSolutionU_of_poly (N : St → P) (Dc : P) (hD : Dc ≠ 0)
    (hrec : ∀ s ∈ recStates, 15 * lhsU s * N s
      = rhsC 30 (5 * tAU) (10 * tAU) (6 * tBU) (9 * tBU) (30 * rhoPU) N s)
    (hbd : ∀ s ∈ bdryStates, N s = C (bdryC piA0F piA1F piB0F piB1F s) * Dc) :
    IsSolutionU (fun s => algebraMap P L (N s) * (algebraMap P L Dc)⁻¹) := by
  have hDL : algebraMap P L Dc ≠ 0 := algebraMap_ne_zero hD
  constructor
  · intro s hs
    have h := congrArg (algebraMap P L) (hrec s hs)
    rw [map_mul, map_mul, rhsC_map] at h
    simp only [algebraMap_lhsU, algebraMap_tAU, algebraMap_tBU, algebraMap_rhoPU, map_mul,
      map_ofNat] at h
    rw [rhsC_LU_scaled] at h
    change lhsC thAu thBu rhoU s * (algebraMap P L (N s) * (algebraMap P L Dc)⁻¹) = _
    rw [rhsC_mul_const]
    linear_combination ((algebraMap P L Dc)⁻¹ / 30) * h
  · intro s hs
    have h := congrArg (algebraMap P L) (hbd s hs)
    rw [map_mul, algebraMap_P_C, bdryC_map] at h
    simp only [algebraMap_piA0F, algebraMap_piA1F, algebraMap_piB0F, algebraMap_piB1F] at h
    change algebraMap P L (N s) * (algebraMap P L Dc)⁻¹ = _
    rw [h]
    exact mul_inv_cancel_right₀ (G₀ := L) hDL _

noncomputable def qSolU (s : St) : L := algebraMap P L (ValU s) * (algebraMap P L DcomU)⁻¹

end Rhone.Algebra.KilledSystemULast
