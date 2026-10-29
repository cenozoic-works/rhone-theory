/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Data

/-! # From a polynomial certificate to a solution of the system -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

open Polynomial

noncomputable def thAP : P := C thAF
noncomputable def thBP : P := C thBF
noncomputable def rhoP : P := X

theorem algebraMap_P_C (x : Fuv) : algebraMap P L (C x) = algebraMap Fuv L x :=
  RatFunc.algebraMap_C x

@[simp] theorem algebraMap_thAP : algebraMap P L thAP = thA := RatFunc.algebraMap_C _
@[simp] theorem algebraMap_thBP : algebraMap P L thBP = thB := RatFunc.algebraMap_C _
@[simp] theorem algebraMap_rhoP : algebraMap P L rhoP = rhoL := RatFunc.algebraMap_X

@[simp] theorem algebraMap_piA0F : algebraMap Fuv L piA0F = piA0 := by
  rw [piA0F, piA0, map_div₀, map_one, map_ofNat]

@[simp] theorem algebraMap_piA1F : algebraMap Fuv L piA1F = piA1 := by
  rw [piA1F, piA1, map_div₀, map_ofNat, map_ofNat]

@[simp] theorem algebraMap_piB0F : algebraMap Fuv L piB0F = piB0 := by
  rw [piB0F, piB0, map_div₀, map_ofNat, map_ofNat]

@[simp] theorem algebraMap_piB1F : algebraMap Fuv L piB1F = piB1 := by
  rw [piB1F, piB1, map_div₀, map_ofNat, map_ofNat]

theorem quad_smul (r a2 a1 a0 b2 b1 b0 : Fuv) (h2 : a2 = r * b2) (h1 : a1 = r * b1)
    (h0 : a0 = r * b0) :
    C a2 * X ^ 2 + C a1 * X + C a0 = C r * (C b2 * X ^ 2 + C b1 * X + C b0) := by
  subst h2; subst h1; subst h0
  simp only [map_mul]
  ring

theorem rhsC_L_scaled (F : St → L) (s : St) :
    rhsC 15 (5 * thA) (10 * thA) (6 * thB) (9 * thB) (15 * rhoL) F s
      = 15 * rhsC 1 (thA * piA0) (thA * piA1) (thB * piB0) (thB * piB1) rhoL F s := by
  have h := rhsC_scale (15 : L) 1 (thA * piA0) (thA * piA1) (thB * piB0) (thB * piB1) rhoL F s
  rw [show ((15 : L) * 1) = 15 from by ring] at h
  rw [show ((15 : L) * (thA * piA0)) = 5 * thA from by rw [piA0]; ring] at h
  rw [show ((15 : L) * (thA * piA1)) = 10 * thA from by rw [piA1]; ring] at h
  rw [show ((15 : L) * (thB * piB0)) = 6 * thB from by rw [piB0]; ring] at h
  rw [show ((15 : L) * (thB * piB1)) = 9 * thB from by rw [piB1]; ring] at h
  exact h

theorem Dcom_ne_zero : Dcom ≠ 0 := by
  have hlead : (225 * thAF ^ 2 * thBF + 225 * thAF ^ 2 + 225 * thAF * thBF ^ 2 +
      900 * thAF * thBF + 675 * thAF + 225 * thBF ^ 2 + 675 * thBF + 450 : Fuv)
      = 225 * ((thAF + 1) * ((thBF + 1) * (thAF + thBF + 2))) := by ring
  intro h
  have h2 := congrArg (fun p => Polynomial.coeff p 2) h
  simp only [Dcom, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at h2
  norm_num [hlead] at h2
  rcases h2 with h2 | h2 | h2
  · exact thAF_add_one_ne_zero h2
  · exact thBF_add_one_ne_zero h2
  · exact thAF_add_thBF_add_two_ne_zero h2

theorem Dcom_L_ne_zero : algebraMap P L Dcom ≠ 0 := algebraMap_ne_zero Dcom_ne_zero

theorem isSolution_of_poly (N : St → P) (Dc : P) (hD : Dc ≠ 0)
    (hrec : ∀ s ∈ recStates, 15 * lhsC thAP thBP rhoP s * N s
      = rhsC 15 (5 * thAP) (10 * thAP) (6 * thBP) (9 * thBP) (15 * rhoP) N s)
    (hbd : ∀ s ∈ bdryStates, N s = C (bdryC piA0F piA1F piB0F piB1F s) * Dc) :
    IsSolution (fun s => algebraMap P L (N s) * (algebraMap P L Dc)⁻¹) := by
  have hDL : algebraMap P L Dc ≠ 0 := algebraMap_ne_zero hD
  constructor
  · intro s hs
    have h := congrArg (algebraMap P L) (hrec s hs)
    rw [map_mul, map_mul, lhsC_map, rhsC_map] at h
    simp only [algebraMap_thAP, algebraMap_thBP, algebraMap_rhoP, map_mul, map_ofNat] at h
    rw [rhsC_L_scaled] at h
    change lhsC thA thB rhoL s * (algebraMap P L (N s) * (algebraMap P L Dc)⁻¹) = _
    rw [rhsC_mul_const]
    linear_combination ((algebraMap P L Dc)⁻¹ / 15) * h
  · intro s hs
    have h := congrArg (algebraMap P L) (hbd s hs)
    rw [map_mul, algebraMap_P_C, bdryC_map] at h
    simp only [algebraMap_piA0F, algebraMap_piA1F, algebraMap_piB0F, algebraMap_piB1F] at h
    change algebraMap P L (N s) * (algebraMap P L Dc)⁻¹ = _
    rw [h, mul_inv_cancel_right₀ hDL]

noncomputable def qSol (s : St) : L := algebraMap P L (Val s) * (algebraMap P L Dcom)⁻¹

end Rhone.Algebra.KilledSystem
