/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Upper

/-! # The `W`-orthonormal eigenbasis, and every eigenvalue is real and above the floor -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset

variable {i j : ℕ} {θA θB ρ lam : ℝ}

noncomputable def eigWval (i j : ℕ) (θA θB : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (k : Fin (min i j + 1)) : ℝ :=
  (symT_isHermitian (i := i) (j := j) (θA := θA) (θB := θB) hρ).eigenvalues k

noncomputable def eigW (i j : ℕ) (θA θB : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (k : Fin (min i j + 1)) :
    Fin (min i j + 1) → ℝ :=
  psi i j ρ (eigVec (symT_isHermitian (i := i) (j := j) (θA := θA) (θB := θB) hρ) k)

theorem phi_eigW (hρ : 0 < ρ) (k : Fin (min i j + 1)) :
    phi i j ρ (eigW i j θA θB hρ k) =
      eigVec (symT_isHermitian (i := i) (j := j) (θA := θA) (θB := θB) hρ) k :=
  phi_psi hρ _

theorem mulVec_eigW (hρ : 0 < ρ) (k : Fin (min i j + 1)) :
    T i j θA θB ρ *ᵥ eigW i j θA θB hρ k = eigWval i j θA θB hρ k • eigW i j θA θB hρ k := by
  rw [← mulVec_symT_iff (θA := θA) (θB := θB) hρ, phi_eigW]
  exact mulVec_eigVec _ k

theorem eigW_ne_zero (hρ : 0 < ρ) (k : Fin (min i j + 1)) : eigW i j θA θB hρ k ≠ 0 :=
  psi_ne_zero hρ (eigVec_ne_zero _ k)

theorem innerW_eigW (hρ : 0 < ρ) (k l : Fin (min i j + 1)) :
    innerW i j ρ (eigW i j θA θB hρ k) (eigW i j θA θB hρ l) = if k = l then 1 else 0 := by
  rw [← phi_dotProduct hρ, phi_eigW, phi_eigW]
  exact eigVec_dotProduct _ k l

theorem eigW_sum_repr (hρ : 0 < ρ) (u : Fin (min i j + 1) → ℝ) :
    ∑ k, innerW i j ρ (eigW i j θA θB hρ k) u • eigW i j θA θB hρ k = u := by
  set hH := symT_isHermitian (i := i) (j := j) (θA := θA) (θB := θB) hρ with hH_def
  have hcoef : ∀ k, innerW i j ρ (eigW i j θA θB hρ k) u = eigVec hH k ⬝ᵥ phi i j ρ u := by
    intro k
    rw [← phi_dotProduct hρ, phi_eigW]
  have key : ∑ k, innerW i j ρ (eigW i j θA θB hρ k) u • eigW i j θA θB hρ k
      = ∑ k, (eigVec hH k ⬝ᵥ phi i j ρ u) • psi i j ρ (eigVec hH k) :=
    Finset.sum_congr rfl fun k _ => by rw [hcoef k]; rfl
  have hswap : ∑ k, (eigVec hH k ⬝ᵥ phi i j ρ u) • psi i j ρ (eigVec hH k)
      = psi i j ρ (∑ k, (eigVec hH k ⬝ᵥ phi i j ρ u) • eigVec hH k) := by
    funext t
    simp only [psi, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [key, hswap, eigVec_sum_repr hH (phi i j ρ u), psi_phi hρ]

theorem innerW_expansion (hρ : 0 < ρ) (u v : Fin (min i j + 1) → ℝ) :
    ∑ k, innerW i j ρ (eigW i j θA θB hρ k) u * innerW i j ρ (eigW i j θA θB hρ k) v
      = innerW i j ρ u v := by
  have hcoef : ∀ (w : Fin (min i j + 1) → ℝ) (k), innerW i j ρ (eigW i j θA θB hρ k) w
      = eigVec (symT_isHermitian (i := i) (j := j) (θA := θA) (θB := θB) hρ) k ⬝ᵥ phi i j ρ w := by
    intro w k
    rw [← phi_dotProduct hρ, phi_eigW]
  simp only [hcoef]
  rw [dotProduct_eigVec_eq, phi_dotProduct hρ]

theorem TeSpec_eq_spectrum (i j : ℕ) (lam θA θB ρ : ℝ) :
    TeSpec i j lam θA θB ρ = spectrum ℝ (Te i j lam θA θB ρ) := by
  ext c
  rw [mem_spectrum_iff_exists_eigenvector]
  rfl

theorem mem_TeSpec_iff_hasEigenvalue (i j : ℕ) (lam θA θB ρ : ℝ) (c : ℝ) :
    c ∈ TeSpec i j lam θA θB ρ ↔
      Module.End.HasEigenvalue (Matrix.toLin' (Te i j lam θA θB ρ)) c :=
  (hasEigenvalue_toLin'_iff _ _).symm

theorem Te_spectrum_ge_floor (hlam : 0 < lam) (hρ : 0 ≤ ρ) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ (Te i j lam θA θB ρ)) : floorMu i j θA θB ≤ μ := by
  rw [← TeSpec_eq_spectrum] at hμ
  obtain ⟨v, hv, hveq⟩ := hμ
  exact Te_eigen_ge_floor hlam hρ hv hveq

theorem Te_spectrum_ge_sharp (hlam : 0 < lam) (hρ : 0 ≤ ρ) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ (Te i j lam θA θB ρ)) :
    floorMu i j θA θB
        + (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam ≤ μ := by
  rw [← TeSpec_eq_spectrum] at hμ
  obtain ⟨v, hv, hveq⟩ := hμ
  exact Te_eigen_ge_sharp hlam hρ hv hveq

theorem Te_complex_eigen_scale (hlam : lam ≠ 0) {z : ℂ} {v : Fin (min i j + 1) → ℂ}
    (heig : ∀ t, ∑ s, ((Te i j lam θA θB ρ t s : ℝ) : ℂ) * v s = z * v t) (t) :
    ∑ s, ((T i j (lam * θA) (lam * θB) (lam * ρ) t s : ℝ) : ℂ) * v s = (lam * z) * v t := by
  have hs : ∀ s, ((T i j (lam * θA) (lam * θB) (lam * ρ) t s : ℝ) : ℂ)
      = (lam : ℂ) * ((Te i j lam θA θB ρ t s : ℝ) : ℂ) := by
    intro s
    have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    have hTe : Te i j lam θA θB ρ t s = lam⁻¹ * T i j (lam * θA) (lam * θB) (lam * ρ) t s := rfl
    rw [hTe]
    push_cast
    field_simp
  simp only [hs, mul_assoc, ← Finset.mul_sum, heig t]

theorem Te_complex_eigen_real (hlam : 0 < lam) (hρ : 0 < ρ) {z : ℂ}
    {v : Fin (min i j + 1) → ℂ} (hv : v ≠ 0)
    (heig : ∀ t, ∑ s, ((Te i j lam θA θB ρ t s : ℝ) : ℂ) * v s = z * v t) : z.im = 0 := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have h := eigen_im_eq_zero (i := i) (j := j) (θA := lam * θA) (θB := lam * θB)
    (ρ := lam * ρ) (mul_pos hlam hρ) hv (Te_complex_eigen_scale hlam' heig)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h
  rcases mul_eq_zero.1 h with h' | h'
  · exact absurd h' hlam'
  · exact h'

theorem Te_complex_eigen_ge_floor (hlam : 0 < lam) (hρ : 0 < ρ) {z : ℂ}
    {v : Fin (min i j + 1) → ℂ} (hv : v ≠ 0)
    (heig : ∀ t, ∑ s, ((Te i j lam θA θB ρ t s : ℝ) : ℂ) * v s = z * v t) :
    z.im = 0 ∧ floorMu i j θA θB ≤ z.re := by
  refine ⟨Te_complex_eigen_real hlam hρ hv heig, ?_⟩
  have hre : ∀ t, (Te i j lam θA θB ρ *ᵥ fun s => (v s).re) t = z.re * (v t).re := by
    intro t
    have h := congrArg Complex.re (heig t)
    simpa [mulVec_apply, Complex.add_re, Complex.mul_re, Te_complex_eigen_real hlam hρ hv heig]
      using h
  have him : ∀ t, (Te i j lam θA θB ρ *ᵥ fun s => (v s).im) t = z.re * (v t).im := by
    intro t
    have h := congrArg Complex.im (heig t)
    simpa [mulVec_apply, Complex.add_im, Complex.mul_im,
      Te_complex_eigen_real hlam hρ hv heig] using h
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hv
  have hvt : v t ≠ 0 := by simpa using ht
  by_cases hrez : (fun s => (v s).re) = (0 : Fin (min i j + 1) → ℝ)
  · have hime : (fun s => (v s).im) ≠ (0 : Fin (min i j + 1) → ℝ) := by
      intro hc
      refine hvt (Complex.ext ?_ ?_)
      · simpa using congrFun hrez t
      · simpa using congrFun hc t
    refine Te_eigen_ge_floor hlam hρ.le hime ?_
    funext s
    rw [him s]
    rfl
  · refine Te_eigen_ge_floor hlam hρ.le hrez ?_
    funext s
    rw [hre s]
    rfl

end Rhone.LinearAlgebra.Spectral
