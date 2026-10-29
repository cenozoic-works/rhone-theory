/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.AlleleLumping.Defs

/-! # The Cramer form of the sampling probability, for every number of alleles -/

@[expose] public section

namespace Rhone.LinearAlgebra.AlleleLumping

open Finset Matrix Recursion

variable {KA KB : ℕ} {F : Type*} [Field F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem Tmat_mulVec (N : ℕ) (v : Lev KA KB N → F) :
    Tmat θA θB ρ πA πB N *ᵥ v = blockOp θA θB ρ πA πB N v := by
  rw [Tmat, LinearMap.toMatrix'_mulVec]

theorem src_congr (N : ℕ) {q₁ q₂ : Config KA KB → F}
    (h : ∀ η : Config KA KB, η.nA + η.nB < N → q₁ η = q₂ η) :
    src θA θB ρ πA πB q₁ N = src θA θB ρ πA πB q₂ N := by
  have hb : below N q₁ = below N q₂ := by
    funext η
    simp only [below]
    split_ifs with hη
    · exact h η hη
    · rfl
  funext ξ
  simp only [src, hb]

theorem blockOp_restrict {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) (N : ℕ) :
    blockOp θA θB ρ πA πB N (fun ξ : Lev KA KB N => q ξ) = src θA θB ρ πA πB q N := by
  funext ξ
  have hξ : (ξ : Config KA KB).nA + (ξ : Config KA KB).nB = N := ξ.2
  rw [blockOp_apply]
  simp only [src]
  split_ifs with hn
  · have hsplit : q = fun η => extZero N (fun ζ : Lev KA KB N => q ζ) η + offLevel N q η := by
      funext η
      simp only [extZero, offLevel]
      by_cases h : η.nA + η.nB = N <;> simp [h]
    have h1 : rhs θA θB ρ πA πB q (ξ : Config KA KB)
        = rhs θA θB ρ πA πB (extZero N (fun ζ : Lev KA KB N => q ζ)) (ξ : Config KA KB)
          + rhs θA θB ρ πA πB (offLevel N q) (ξ : Config KA KB) := by
      conv_lhs => rw [hsplit]
      rw [rhs_add]
    have h2 : rhs θA θB ρ πA πB (offLevel N q) (ξ : Config KA KB)
        = rhs θA θB ρ πA πB (below N q) (ξ : Config KA KB) := by
      refine rhs_congr θA θB ρ πA πB (ξ : Config KA KB) fun η hA hB => ?_
      simp only [offLevel, below]
      split_ifs <;> first | rfl | omega
    rw [hq.recursion _ hn, h1, h2]
    ring
  · rcases Nat.lt_or_ge (ξ : Config KA KB).n 1 with h | h
    · have hz : (ξ : Config KA KB) = 0 := Config.eq_zero_of_n_eq_zero _ (by omega)
      rw [hz, hq.empty, Config.bdryVal_zero]
    · rcases Config.exists_e_of_n_eq_one (ξ : Config KA KB) (by omega) with
        ⟨i, hi⟩ | ⟨j, hj⟩ | ⟨i, j, hij⟩
      · rw [hi, hq.bdryA, Config.bdryVal_eA]
      · rw [hj, hq.bdryB, Config.bdryVal_eB]
      · rw [hij, hq.bdryC, Config.bdryVal_eC]

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem Tmat_isUnit (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    IsUnit (Tmat θA θB ρ πA πB N : Matrix (Lev KA KB N) (Lev KA KB N) F) := by
  refine Matrix.mulVec_injective_iff_isUnit.mp fun v w h => ?_
  simp only [Tmat_mulVec] at h
  exact blockOp_injective hθA hθB hρ N h

theorem Tmat_det_ne_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    (Tmat θA θB ρ πA πB N : Matrix (Lev KA KB N) (Lev KA KB N) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Tmat_isUnit hθA hθB hρ N)).ne_zero

theorem cramer_form {q : Config KA KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (N : ℕ) :
    (Tmat θA θB ρ πA πB N).det ≠ 0
      ∧ (fun ξ : Lev KA KB N => q ξ)
          = (Tmat θA θB ρ πA πB N)⁻¹ *ᵥ src θA θB ρ πA πB q N
      ∧ ∀ ξ : Lev KA KB N,
          q ξ = Matrix.cramer (Tmat θA θB ρ πA πB N) (src θA θB ρ πA πB q N) ξ
            / (Tmat θA θB ρ πA πB N).det := by
  have hdet := Tmat_det_ne_zero (πA := πA) (πB := πB) hθA hθB hρ N
  have hunit : IsUnit (Tmat θA θB ρ πA πB N).det := isUnit_iff_ne_zero.mpr hdet
  have hsys : Tmat θA θB ρ πA πB N *ᵥ (fun ξ : Lev KA KB N => q ξ)
      = src θA θB ρ πA πB q N := by
    rw [Tmat_mulVec, blockOp_restrict hq]
  have hinv : (fun ξ : Lev KA KB N => q ξ)
      = (Tmat θA θB ρ πA πB N)⁻¹ *ᵥ src θA θB ρ πA πB q N := by
    rw [← hsys, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  refine ⟨hdet, hinv, fun ξ => ?_⟩
  have h := congrFun hinv ξ
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec,
    ← Matrix.cramer_eq_adjugate_mulVec, Pi.smul_apply, smul_eq_mul] at h
  rw [h, div_eq_inv_mul]

end Rhone.LinearAlgebra.AlleleLumping
