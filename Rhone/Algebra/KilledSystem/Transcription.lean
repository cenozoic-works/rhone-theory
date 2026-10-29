/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Data
public import Rhone.Algebra.Q22Data

/-! # Coefficientwise comparison of the unchanged archive transcriptions -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

open Polynomial

theorem V46_coeff_scale_2 : 4 * V46.coeff 2 = 3 * qN2 := by
  norm_num only [V46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp only [qN2, uu_eq, vv_eq]
  ring

theorem V46_coeff_scale_1 : 4 * V46.coeff 1 = 3 * qN1 := by
  norm_num only [V46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp only [qN1, uu_eq, vv_eq]
  ring

theorem V46_coeff_scale_0 : 4 * V46.coeff 0 = 3 * qN0 := by
  norm_num only [V46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp only [qN0, uu_eq, vv_eq]
  ring

theorem V46_transcription_scale : 4 * V46 = 3 * Nq := by
  ext n
  by_cases h2 : n = 2
  · subst n
    simpa [Nq] using V46_coeff_scale_2
  by_cases h1 : n = 1
  · subst n
    simpa [Nq] using V46_coeff_scale_1
  by_cases h0 : n = 0
  · subst n
    simpa [Nq] using V46_coeff_scale_0
  simp only [V46, Nq, coeff_ofNat_mul, coeff_add, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_C, h2, h1, h0, ite_false, mul_zero, add_zero]

theorem Dcom_coeff_scale_2 : 4 * Dcom.coeff 2 = 3 * qD2 := by
  norm_num only [Dcom, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp only [qD2, uu_eq, vv_eq]
  ring

theorem Dcom_coeff_scale_1 : 4 * Dcom.coeff 1 = 3 * qD1 := by
  norm_num only [Dcom, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp only [qD1, uu_eq, vv_eq]
  ring

theorem Dcom_coeff_scale_0 : 4 * Dcom.coeff 0 = 3 * qD0 := by
  norm_num only [Dcom, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp only [qD0, uu_eq, vv_eq]
  ring

theorem Dcom_transcription_scale : 4 * Dcom = 3 * Dq := by
  ext n
  by_cases h2 : n = 2
  · subst n
    simpa [Dq] using Dcom_coeff_scale_2
  by_cases h1 : n = 1
  · subst n
    simpa [Dq] using Dcom_coeff_scale_1
  by_cases h0 : n = 0
  · subst n
    simpa [Dq] using Dcom_coeff_scale_0
  simp only [Dcom, Dq, coeff_ofNat_mul, coeff_add, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_C, h2, h1, h0, ite_false, mul_zero, add_zero]

end Rhone.Algebra.KilledSystem
