/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Tactic.FieldSimp

/-! # The epoch operator is the same tridiagonal family, rescaled -/

@[expose] public section

namespace Rhone.LinearAlgebra.Tridiag

open Matrix

variable {F : Type*} [Field F]

noncomputable def Tepoch (i j : ℕ) (lam θA θB ρ : F) :
    Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) F :=
  (1 / lam) • Tcoal F i j + θA • TmutA F i j + θB • TmutB F i j + ρ • Trec F i j

theorem Tepoch_eq_smul_T (i j : ℕ) {lam : F} (hlam : lam ≠ 0) (θA θB ρ : F) :
    Tepoch i j lam θA θB ρ = (1 / lam) • T F i j (lam * θA) (lam * θB) (lam * ρ) := by
  rw [Tepoch, T_eq_classes, smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
    show 1 / lam * (lam * θA) = θA from by field_simp,
    show 1 / lam * (lam * θB) = θB from by field_simp,
    show 1 / lam * (lam * ρ) = ρ from by field_simp]

theorem T_smul_eq_Tepoch (i j : ℕ) {lam : F} (hlam : lam ≠ 0) (θA θB ρ : F) :
    T F i j (lam * θA) (lam * θB) (lam * ρ) = lam • Tepoch i j lam θA θB ρ := by
  rw [Tepoch_eq_smul_T i j hlam, smul_smul, mul_one_div, div_self hlam, one_smul]

theorem epoch_propagator_exponent (i j : ℕ) {lam : F} (hlam : lam ≠ 0) (θA θB ρ Δ : F) :
    (-(Δ / 2)) • Tepoch i j lam θA θB ρ
      = (-(Δ / (2 * lam))) • T F i j (lam * θA) (lam * θB) (lam * ρ) := by
  rw [Tepoch_eq_smul_T i j hlam, smul_smul]
  congr 1
  field_simp

theorem epoch_mulVec_iff (i j : ℕ) {lam : F} (hlam : lam ≠ 0) (θA θB ρ : F)
    (Φ R : Fin (min i j + 1) → F) :
    Tepoch i j lam θA θB ρ *ᵥ Φ = (1 / lam) • R
      ↔ T F i j (lam * θA) (lam * θB) (lam * ρ) *ᵥ Φ = R := by
  have hinv : (1 / lam) ≠ 0 := one_div_ne_zero hlam
  rw [Tepoch_eq_smul_T i j hlam, Matrix.smul_mulVec]
  exact smul_right_injective _ hinv |>.eq_iff

theorem det_Tepoch (i j : ℕ) {lam : F} (hlam : lam ≠ 0) (θA θB ρ : F) :
    (Tepoch i j lam θA θB ρ).det
      = (1 / lam) ^ (min i j + 1) * E F i j (lam * θA) (lam * θB) (lam * ρ) := by
  rw [Tepoch_eq_smul_T i j hlam, Matrix.det_smul, Fintype.card_fin, E]

end Rhone.LinearAlgebra.Tridiag
