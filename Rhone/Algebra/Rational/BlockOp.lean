/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Rational.Map

/-! # The level operator of the killed-PIM system over an arbitrary commutative ring -/

@[expose] public section

namespace Rhone.Algebra.Rational

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {R S : Type*} [CommRing R] [CommRing S]

abbrev Lvl (KA KB N : ℕ) := ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N}

noncomputable instance instDecidableEqLvl (N : ℕ) : DecidableEq (Lvl KA KB N) :=
  Classical.decEq _

def extZ (N : ℕ) (v : Lvl KA KB N → R) : Config KA KB → R :=
  fun η => if h : η.nA + η.nB = N then v ⟨η, h⟩ else 0

theorem extZ_of_mem (N : ℕ) (v : Lvl KA KB N → R) (η : Config KA KB)
    (h : η.nA + η.nB = N) : extZ N v η = v ⟨η, h⟩ := by
  simp [extZ, h]

theorem extZ_of_not_mem (N : ℕ) (v : Lvl KA KB N → R) {η : Config KA KB}
    (h : η.nA + η.nB ≠ N) : extZ N v η = 0 := by
  simp [extZ, h]

noncomputable def bOp (θA θB ρ : R) (πA : Fin KA → R) (πB : Fin KB → R) (N : ℕ) :
    (Lvl KA KB N → R) →ₗ[R] (Lvl KA KB N → R) where
  toFun v := fun ξ =>
    if 2 ≤ (ξ : Config KA KB).n
      then diag θA θB ρ (ξ : Config KA KB) * v ξ
        - rhs θA θB ρ πA πB (extZ N v) (ξ : Config KA KB)
      else v ξ
  map_add' v w := by
    have hext : extZ N (v + w) = fun η => extZ N v η + extZ N w η := by
      funext η; simp only [extZ]; split_ifs <;> simp
    funext ξ
    simp only [Pi.add_apply, hext, rhs_add]
    split_ifs with hn
    · ring
    · rfl
  map_smul' c v := by
    have hext : extZ N (c • v) = fun η => c * extZ N v η := by
      funext η; simp only [extZ]; split_ifs <;> simp
    funext ξ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hext, rhs_smul]
    split_ifs with hn
    · ring
    · rfl

theorem bOp_apply (θA θB ρ : R) (πA : Fin KA → R) (πB : Fin KB → R) (N : ℕ)
    (v : Lvl KA KB N → R) (ξ : Lvl KA KB N) :
    bOp θA θB ρ πA πB N v ξ =
      if 2 ≤ (ξ : Config KA KB).n
        then diag θA θB ρ (ξ : Config KA KB) * v ξ
          - rhs θA θB ρ πA πB (extZ N v) (ξ : Config KA KB)
        else v ξ := rfl

theorem extZ_map (φ : R →+* S) (N : ℕ) (v : Lvl KA KB N → R) :
    (fun η => φ (extZ N v η)) = extZ N (fun η => φ (v η)) := by
  funext η
  simp only [extZ]
  split_ifs <;> simp

theorem bOp_map (φ : R →+* S) (θA θB ρ : R) (πA : Fin KA → R) (πB : Fin KB → R) (N : ℕ)
    (v : Lvl KA KB N → R) (ξ : Lvl KA KB N) :
    φ (bOp θA θB ρ πA πB N v ξ)
      = bOp (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j)) N
          (fun η => φ (v η)) ξ := by
  rw [bOp_apply, bOp_apply]
  split_ifs with hn
  · rw [map_sub, map_mul, diag_map φ, rhs_map φ, extZ_map φ]
  · rfl

noncomputable def bMat (θA θB ρ : R) (πA : Fin KA → R) (πB : Fin KB → R) (N : ℕ) :
    Matrix (Lvl KA KB N) (Lvl KA KB N) R :=
  fun ξ η => bOp θA θB ρ πA πB N (Pi.single η 1) ξ

theorem bOp_apply_eq_sum (θA θB ρ : R) (πA : Fin KA → R) (πB : Fin KB → R) (N : ℕ)
    (v : Lvl KA KB N → R) (ξ : Lvl KA KB N) :
    bOp θA θB ρ πA πB N v ξ = ∑ η, bMat θA θB ρ πA πB N ξ η * v η := by
  have hv : v = ∑ η, v η • (Pi.single η (1 : R)) := by
    funext ζ
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bMat]
  exact Finset.sum_congr rfl fun η _ => mul_comm _ _

theorem bOp_eq_mulVec (θA θB ρ : R) (πA : Fin KA → R) (πB : Fin KB → R) (N : ℕ)
    (v : Lvl KA KB N → R) :
    (fun ξ => bOp θA θB ρ πA πB N v ξ) = Matrix.mulVec (bMat θA θB ρ πA πB N) v := by
  funext ξ
  rw [bOp_apply_eq_sum]
  simp [Matrix.mulVec, dotProduct]

theorem bMat_map (φ : R →+* S) (θA θB ρ : R) (πA : Fin KA → R) (πB : Fin KB → R) (N : ℕ) :
    (bMat θA θB ρ πA πB N).map φ
      = bMat (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j)) N := by
  ext ξ η
  have h1 : (fun ζ => φ ((Pi.single η (1 : R) : Lvl KA KB N → R) ζ))
      = (Pi.single η (1 : S) : Lvl KA KB N → S) := by
    funext ζ
    simp only [Pi.single_apply]
    split_ifs <;> simp
  simp only [Matrix.map_apply, bMat]
  rw [bOp_map φ, h1]

section Ordered

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem bOp_injective_of_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    Function.Injective (bOp θA θB ρ πA πB N) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 2 ≤ η.n
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhs θA θB ρ πA πB (extZ N v) η
        else v ⟨η, hη⟩) = 0 := fun η hη => congrFun hv ⟨η, hη⟩
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → extZ N v ξ = 0 := by
    intro ξ hn _
    by_cases hl : ξ.nA + ξ.nB = N
    · have h3 := hv' ξ hl
      rw [ite_eq_right (show ¬ (2 ≤ ξ.n) by omega)] at h3
      rw [extZ_of_mem N v ξ hl]; exact h3
    · exact extZ_of_not_mem N v hl
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * extZ N v ξ = rhs θA θB ρ πA πB (extZ N v) ξ := by
    intro ξ hn hl
    by_cases hlev : ξ.nA + ξ.nB = N
    · have h2 := hv' ξ hlev
      rw [ite_eq_left hn] at h2
      rw [extZ_of_mem N v ξ hlev]
      linarith [h2]
    · have hb : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → extZ N v η = 0 :=
        fun η h1 h2 => extZ_of_not_mem N v (by omega)
      rw [extZ_of_not_mem N v hlev, mul_zero,
        rhs_congr θA θB ρ πA πB (q₂ := fun _ => (0 : F)) ξ hb, rhs_zero]
  have key := homogeneous_eq_zero_le (πA := πA) (πB := πB) hθA hθB hρ hbd hrec
  funext ξ
  have := key ξ (le_of_eq ξ.2)
  rw [extZ_of_mem N v ξ ξ.2] at this
  simpa using this

theorem det_bMat_ne_zero_of_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    (bMat θA θB ρ πA πB N).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine hv0 (bOp_injective_of_pos (πA := πA) (πB := πB) hθA hθB hρ N ?_)
  rw [map_zero]
  funext ξ
  have hmv := congrFun (bOp_eq_mulVec θA θB ρ πA πB N v) ξ
  rw [hmv, hv]

end Ordered

theorem det_bMat_ne_zero_of_hom {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : R} {πA : Fin KA → R} {πB : Fin KB → R} (φ : R →+* F)
    (hθA : 0 < φ θA) (hθB : 0 < φ θB) (hρ : 0 ≤ φ ρ) (N : ℕ) :
    (bMat θA θB ρ πA πB N).det ≠ 0 := by
  intro hdet
  have h1 : φ ((bMat θA θB ρ πA πB N).det) = 0 := by rw [hdet, map_zero]
  rw [RingHom.map_det φ] at h1
  have h2 : (φ.mapMatrix (bMat θA θB ρ πA πB N))
      = bMat (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j)) N := by
    rw [RingHom.mapMatrix_apply, bMat_map]
  rw [h2] at h1
  exact det_bMat_ne_zero_of_pos hθA hθB hρ N h1

theorem bOp_injective_of_det_ne_zero {F : Type*} [Field F] {θA θB ρ : F} {πA : Fin KA → F}
    {πB : Fin KB → F} (N : ℕ) (h : (bMat θA θB ρ πA πB N).det ≠ 0) :
    Function.Injective (bOp θA θB ρ πA πB N) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hv0
  refine h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩)
  rw [← bOp_eq_mulVec]
  funext ξ
  exact congrFun hv ξ

end Rhone.Algebra.Rational
