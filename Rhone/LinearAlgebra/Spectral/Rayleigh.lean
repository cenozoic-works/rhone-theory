/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! # Real symmetric matrices: eigenbasis, Rayleigh quotient, and the bridge to `spectrum` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

section EigenBasis

variable [DecidableEq n]

noncomputable def eigVec (hA : A.IsHermitian) (k : n) : n → ℝ := ⇑(hA.eigenvectorBasis k)

theorem mulVec_eigVec (hA : A.IsHermitian) (k : n) :
    A *ᵥ eigVec hA k = hA.eigenvalues k • eigVec hA k :=
  hA.mulVec_eigenvectorBasis k

theorem dotProduct_eigVec_eq (hA : A.IsHermitian) (x y : n → ℝ) :
    ∑ k, (eigVec hA k ⬝ᵥ x) * (eigVec hA k ⬝ᵥ y) = x ⬝ᵥ y := by
  have h := hA.eigenvectorBasis.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  rw [dotProduct_comm y x] at h
  simp only [eigVec]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => by rw [dotProduct_comm y]

theorem eigVec_dotProduct (hA : A.IsHermitian) (k l : n) :
    eigVec hA k ⬝ᵥ eigVec hA l = if k = l then 1 else 0 := by
  have h := hA.eigenvectorBasis.orthonormal.2 (i := k) (j := l)
  have h1 := hA.eigenvectorBasis.orthonormal.1 k
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl]
    have : ‖hA.eigenvectorBasis k‖ ^ 2 = 1 := by rw [h1]; norm_num
    rw [← this, ← real_inner_self_eq_norm_sq]
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rfl
  · rw [ite_eq_right hkl, ← h hkl, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct_comm]
    rfl

theorem eigVec_ne_zero (hA : A.IsHermitian) (k : n) : eigVec hA k ≠ 0 := by
  intro hz
  have h := eigVec_dotProduct hA k k
  rw [hz, ite_eq_left rfl] at h
  simp at h

theorem dotProduct_self_eq_sum (hA : A.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ x = ∑ k, (eigVec hA k ⬝ᵥ x) ^ 2 := by
  rw [← dotProduct_eigVec_eq hA x x]
  exact Finset.sum_congr rfl fun k _ => (sq _).symm

theorem eigVec_sum_repr (hA : A.IsHermitian) (x : n → ℝ) :
    ∑ k, (eigVec hA k ⬝ᵥ x) • eigVec hA k = x := by
  funext t
  have h := dotProduct_eigVec_eq hA x (Pi.single t 1)
  simp only [dotProduct_single_one] at h
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact h

theorem quadratic_form_eq_sum (hA : A.IsHermitian) (x : n → ℝ) :
    (A *ᵥ x) ⬝ᵥ x = ∑ k, hA.eigenvalues k * (eigVec hA k ⬝ᵥ x) ^ 2 := by
  have hsymm : Aᵀ = A := Matrix.isHermitian_iff_isSymm.mp hA
  have hrow : ∀ k, eigVec hA k ⬝ᵥ (A *ᵥ x) = hA.eigenvalues k * (eigVec hA k ⬝ᵥ x) := by
    intro k
    have hvm : eigVec hA k ᵥ* A = A *ᵥ eigVec hA k := by
      rw [← Matrix.vecMul_transpose A (eigVec hA k), hsymm]
    rw [dotProduct_mulVec, hvm, mulVec_eigVec, smul_dotProduct, smul_eq_mul]
  rw [← dotProduct_eigVec_eq hA (A *ᵥ x) x]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hrow k]
  ring

end EigenBasis

theorem exists_eigenvalue_le_rayleigh [Nonempty n] (hA : A.IsHermitian) (x : n → ℝ) :
    ∃ (ν : ℝ) (v : n → ℝ), v ≠ 0 ∧ A *ᵥ v = ν • v ∧ ν * (x ⬝ᵥ x) ≤ (A *ᵥ x) ⬝ᵥ x := by
  classical
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_min_image (Finset.univ : Finset n) hA.eigenvalues ⟨Classical.arbitrary n, by simp⟩
  refine ⟨hA.eigenvalues k, eigVec hA k, eigVec_ne_zero hA k, mulVec_eigVec hA k, ?_⟩
  rw [quadratic_form_eq_sum hA, dotProduct_self_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  exact mul_le_mul_of_nonneg_right (hk l (Finset.mem_univ l)) (sq_nonneg _)

theorem exists_eigenvalue_ge_rayleigh [Nonempty n] (hA : A.IsHermitian) (x : n → ℝ) :
    ∃ (ν : ℝ) (v : n → ℝ), v ≠ 0 ∧ A *ᵥ v = ν • v ∧ (A *ᵥ x) ⬝ᵥ x ≤ ν * (x ⬝ᵥ x) := by
  classical
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image (Finset.univ : Finset n) hA.eigenvalues ⟨Classical.arbitrary n, by simp⟩
  refine ⟨hA.eigenvalues k, eigVec hA k, eigVec_ne_zero hA k, mulVec_eigVec hA k, ?_⟩
  rw [quadratic_form_eq_sum hA, dotProduct_self_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  exact mul_le_mul_of_nonneg_right (hk l (Finset.mem_univ l)) (sq_nonneg _)

section Bridge

variable [DecidableEq n]

theorem hasEigenvalue_toLin'_iff (B : Matrix n n ℝ) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' B) μ ↔ ∃ v : n → ℝ, v ≠ 0 ∧ B *ᵥ v = μ • v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, by simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.1 hv.1⟩
  · rintro ⟨v, hv, hveq⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [Matrix.toLin'_apply] using hveq

theorem mem_spectrum_iff_exists_eigenvector (B : Matrix n n ℝ) (μ : ℝ) :
    μ ∈ spectrum ℝ B ↔ ∃ v : n → ℝ, v ≠ 0 ∧ B *ᵥ v = μ • v := by
  rw [← hasEigenvalue_toLin'_iff, Module.End.hasEigenvalue_iff_mem_spectrum,
    Matrix.spectrum_toLin']

theorem exists_eigenvector_iff_mem_range (hA : A.IsHermitian) (μ : ℝ) :
    (∃ v : n → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v) ↔ μ ∈ Set.range hA.eigenvalues := by
  rw [← mem_spectrum_iff_exists_eigenvector, hA.spectrum_real_eq_range_eigenvalues]

end Bridge

end Rhone.LinearAlgebra.Spectral
