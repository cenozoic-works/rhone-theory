/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystemULast.Data
public import Rhone.Algebra.Q22uData

/-! # Coefficientwise comparison of the unchanged archive transcriptions -/

@[expose] public section

namespace Rhone.Algebra.KilledSystemULast

open Polynomial

theorem VU46_coeff_scale_5 : VU46.coeff 5 = 3 * nuU5 := by
  norm_num only [VU46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [nuU5]
  ring

theorem VU46_coeff_scale_4 : VU46.coeff 4 = 3 * nuU4 := by
  norm_num only [VU46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [nuU4]
  ring

theorem VU46_coeff_scale_3 : VU46.coeff 3 = 3 * nuU3 := by
  norm_num only [VU46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [nuU3]
  ring

theorem VU46_coeff_scale_2 : VU46.coeff 2 = 3 * nuU2 := by
  norm_num only [VU46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [nuU2]
  ring

theorem VU46_coeff_scale_1 : VU46.coeff 1 = 3 * nuU1 := by
  norm_num only [VU46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [nuU1]
  ring

theorem VU46_coeff_scale_0 : VU46.coeff 0 = 3 * nuU0 := by
  norm_num only [VU46, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [nuU0]
  ring

theorem VU46_transcription_scale : VU46 = 3 * NqU := by
  ext n
  by_cases h5 : n = 5
  · subst n
    simpa [NqU] using VU46_coeff_scale_5
  by_cases h4 : n = 4
  · subst n
    simpa [NqU] using VU46_coeff_scale_4
  by_cases h3 : n = 3
  · subst n
    simpa [NqU] using VU46_coeff_scale_3
  by_cases h2 : n = 2
  · subst n
    simpa [NqU] using VU46_coeff_scale_2
  by_cases h1 : n = 1
  · subst n
    simpa [NqU] using VU46_coeff_scale_1
  by_cases h0 : n = 0
  · subst n
    simpa [NqU] using VU46_coeff_scale_0
  simp only [VU46, NqU, coeff_ofNat_mul, coeff_add, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_C, h5, h4, h3, h2, h1, h0, ite_false, mul_zero, add_zero]

theorem DcomU_coeff_scale_5 : DcomU.coeff 5 = 3 * duU5 := by
  norm_num only [DcomU, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [duU5]
  ring

theorem DcomU_coeff_scale_4 : DcomU.coeff 4 = 3 * duU4 := by
  norm_num only [DcomU, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [duU4]
  ring

theorem DcomU_coeff_scale_3 : DcomU.coeff 3 = 3 * duU3 := by
  norm_num only [DcomU, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [duU3]
  ring

theorem DcomU_coeff_scale_2 : DcomU.coeff 2 = 3 * duU2 := by
  norm_num only [DcomU, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [duU2]
  ring

theorem DcomU_coeff_scale_1 : DcomU.coeff 1 = 3 * duU1 := by
  norm_num only [DcomU, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [duU1]
  ring

theorem DcomU_coeff_scale_0 : DcomU.coeff 0 = 3 * duU0 := by
  norm_num only [DcomU, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [ite_true, ite_false]
  simp [duU0]
  ring

theorem DcomU_transcription_scale : DcomU = 3 * DqU := by
  ext n
  by_cases h5 : n = 5
  · subst n
    simpa [DqU] using DcomU_coeff_scale_5
  by_cases h4 : n = 4
  · subst n
    simpa [DqU] using DcomU_coeff_scale_4
  by_cases h3 : n = 3
  · subst n
    simpa [DqU] using DcomU_coeff_scale_3
  by_cases h2 : n = 2
  · subst n
    simpa [DqU] using DcomU_coeff_scale_2
  by_cases h1 : n = 1
  · subst n
    simpa [DqU] using DcomU_coeff_scale_1
  by_cases h0 : n = 0
  · subst n
    simpa [DqU] using DcomU_coeff_scale_0
  simp only [DcomU, DqU, coeff_ofNat_mul, coeff_add, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_C, h5, h4, h3, h2, h1, h0, ite_false, mul_zero, add_zero]

end Rhone.Algebra.KilledSystemULast
