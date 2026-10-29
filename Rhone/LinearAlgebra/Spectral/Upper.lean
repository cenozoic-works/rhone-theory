/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Conj
public import Rhone.LinearAlgebra.Spectral.Sharp

/-! # Upper end of the spectral floor: `λ_min(T_e) ≤ μ + S/λ` at `ρ_e > 0` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset

variable {i j : ℕ} {θA θB ρ lam : ℝ}

theorem T_exists_eigenvalue_le_rayleighW (hρ : 0 < ρ) (u : Fin (min i j + 1) → ℝ) :
    ∃ (ν : ℝ) (v : Fin (min i j + 1) → ℝ), v ≠ 0 ∧ T i j θA θB ρ *ᵥ v = ν • v ∧
      ν * innerW i j ρ u u ≤ innerW i j ρ (T i j θA θB ρ *ᵥ u) u := by
  obtain ⟨ν, w, hw, hweq, hray⟩ :=
    exists_eigenvalue_le_rayleigh (symT_isHermitian (i := i) (j := j) (θA := θA) (θB := θB) hρ)
      (phi i j ρ u)
  refine ⟨ν, psi i j ρ w, psi_ne_zero (i := i) (j := j) hρ hw, ?_, ?_⟩
  · rw [← mulVec_symT_iff (θA := θA) (θB := θB) hρ, phi_psi hρ]
    exact hweq
  · rw [phi_dotProduct hρ, symT_mulVec_phi (θA := θA) (θB := θB) hρ,
      phi_dotProduct hρ] at hray
    exact hray

theorem one_fun_ne_zero : (fun _ => (1 : ℝ)) ≠ (0 : Fin (min i j + 1) → ℝ) := by
  intro hc
  have := congrFun hc (0 : Fin (min i j + 1))
  norm_num at this

theorem T_exists_eigenvalue_le_sharp (hρ : 0 < ρ) :
    ∃ (ν : ℝ) (v : Fin (min i j + 1) → ℝ), v ≠ 0 ∧ T i j θA θB ρ *ᵥ v = ν • v ∧
      ν ≤ floorMu i j θA θB + bigS (i : ℝ) (j : ℝ) := by
  obtain ⟨ν, v, hv, hveq, hray⟩ :=
    T_exists_eigenvalue_le_rayleighW (i := i) (j := j) (θA := θA) (θB := θB) hρ
      (fun _ => (1 : ℝ))
  refine ⟨ν, v, hv, hveq, ?_⟩
  have hN : 0 < innerW i j ρ (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := innerW_pos hρ one_fun_ne_zero
  have hle := innerW_one_T_one_le (i := i) (j := j) (θA := θA) (θB := θB) hρ
  have hmul : ν * innerW i j ρ (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      ≤ (floorMu i j θA θB + bigS (i : ℝ) (j : ℝ))
        * innerW i j ρ (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := le_trans hray hle
  exact le_of_mul_le_mul_right (by linarith) hN

theorem Te_exists_eigenvalue_le_sharp (hlam : 0 < lam) (hρ : 0 < ρ) :
    ∃ (μ : ℝ) (v : Fin (min i j + 1) → ℝ), v ≠ 0 ∧ Te i j lam θA θB ρ *ᵥ v = μ • v ∧
      μ ≤ floorMu i j θA θB + bigS (i : ℝ) (j : ℝ) / lam := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  obtain ⟨ν, v, hv, hveq, hle⟩ :=
    T_exists_eigenvalue_le_sharp (i := i) (j := j) (θA := lam * θA) (θB := lam * θB)
      (ρ := lam * ρ) (mul_pos hlam hρ)
  refine ⟨ν / lam, v, hv, ?_, ?_⟩
  · rw [Te_mulVec_iff hlam', mul_div_cancel₀ _ hlam']
    exact hveq
  · have hkey : (floorMu i j θA θB + bigS (i : ℝ) (j : ℝ) / lam) * lam
        = floorMu i j (lam * θA) (lam * θB) + bigS (i : ℝ) (j : ℝ) := by
      unfold floorMu
      field_simp
    rw [div_le_iff₀ hlam, hkey]
    exact hle

def TeSpec (i j : ℕ) (lam θA θB ρ : ℝ) : Set ℝ :=
  {c : ℝ | ∃ v : Fin (min i j + 1) → ℝ, v ≠ 0 ∧ Te i j lam θA θB ρ *ᵥ v = c • v}

theorem mem_TeSpec_iff (hlam : lam ≠ 0) {c : ℝ} :
    c ∈ TeSpec i j lam θA θB ρ ↔
      ∃ v : Fin (min i j + 1) → ℝ, v ≠ 0 ∧
        T i j (lam * θA) (lam * θB) (lam * ρ) *ᵥ v = (lam * c) • v := by
  constructor
  · rintro ⟨v, hv, hveq⟩
    exact ⟨v, hv, (Te_mulVec_iff hlam).1 hveq⟩
  · rintro ⟨v, hv, hveq⟩
    exact ⟨v, hv, (Te_mulVec_iff hlam).2 hveq⟩

theorem Te_exists_isLeast (hlam : 0 < lam) (hρ : 0 < ρ) :
    ∃ μ : ℝ, IsLeast (TeSpec i j lam θA θB ρ) μ := by
  classical
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hρ' : 0 < lam * ρ := mul_pos hlam hρ
  set A : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) ℝ :=
    symT i j (lam * θA) (lam * θB) (lam * ρ) with hA_def
  have hA : A.IsHermitian := symT_isHermitian hρ'
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (min i j + 1)))
    hA.eigenvalues ⟨0, Finset.mem_univ 0⟩
  refine ⟨hA.eigenvalues k / lam, ?_, ?_⟩
  · rw [mem_TeSpec_iff hlam', mul_div_cancel₀ _ hlam']
    refine ⟨psi i j (lam * ρ) (eigVec hA k), psi_ne_zero hρ' (eigVec_ne_zero hA k), ?_⟩
    rw [← mulVec_symT_iff (θA := lam * θA) (θB := lam * θB) hρ', phi_psi hρ']
    exact mulVec_eigVec hA k
  · rintro c ⟨v, hv, hveq⟩
    have hc : lam * c ∈ Set.range hA.eigenvalues := by
      rw [← exists_eigenvector_iff_mem_range hA]
      refine ⟨phi i j (lam * ρ) v, phi_ne_zero hρ' hv, ?_⟩
      rw [hA_def, mulVec_symT_iff (θA := lam * θA) (θB := lam * θB) hρ']
      exact (Te_mulVec_iff hlam').1 hveq
    obtain ⟨l, hl⟩ := hc
    have hkl : hA.eigenvalues k ≤ lam * c := hl ▸ hk l (Finset.mem_univ l)
    rw [div_le_iff₀ hlam]
    linarith [hkl]

theorem Te_lambdaMin_sandwich (hlam : 0 < lam) (hρ : 0 < ρ) :
    ∃ μ : ℝ, IsLeast (TeSpec i j lam θA θB ρ) μ ∧
      floorMu i j θA θB
          + (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam ≤ μ ∧
      μ ≤ floorMu i j θA θB + bigS (i : ℝ) (j : ℝ) / lam := by
  obtain ⟨μ, hmem, hlb⟩ := Te_exists_isLeast (i := i) (j := j) (θA := θA) (θB := θB) hlam hρ
  obtain ⟨v, hv, hveq⟩ := hmem
  obtain ⟨ν, w, hw, hweq, hνle⟩ :=
    Te_exists_eigenvalue_le_sharp (i := i) (j := j) (θA := θA) (θB := θB) hlam hρ
  exact ⟨μ, ⟨⟨v, hv, hveq⟩, hlb⟩, Te_eigen_ge_sharp hlam hρ.le hv hveq,
    le_trans (hlb ⟨w, hw, hweq⟩) hνle⟩

theorem Te_lambdaMin_ge_floor (hlam : 0 < lam) (hρ : 0 < ρ) :
    ∃ μ : ℝ, IsLeast (TeSpec i j lam θA θB ρ) μ ∧ floorMu i j θA θB ≤ μ := by
  obtain ⟨μ, hleast, -, -⟩ := Te_lambdaMin_sandwich (i := i) (j := j) (θA := θA) (θB := θB) hlam hρ
  obtain ⟨v, hv, hveq⟩ := hleast.1
  exact ⟨μ, hleast, Te_eigen_ge_floor hlam hρ.le hv hveq⟩

end Rhone.LinearAlgebra.Spectral
