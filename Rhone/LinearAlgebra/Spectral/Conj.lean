/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.SelfAdjoint
public import Rhone.LinearAlgebra.Spectral.Rayleigh

/-! # The unitary conjugation `Φ = D^{-1/2}` between `(⟨·,·⟩_W, T)` and `(·⬝·, S)` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset

variable {i j : ℕ} {θA θB ρ : ℝ}

noncomputable def phi (i j : ℕ) (x : ℝ) (u : Fin (min i j + 1) → ℝ) : Fin (min i j + 1) → ℝ :=
  fun t => u t / Real.sqrt (W i j x (t : ℕ))

noncomputable def psi (i j : ℕ) (x : ℝ) (v : Fin (min i j + 1) → ℝ) : Fin (min i j + 1) → ℝ :=
  fun t => v t * Real.sqrt (W i j x (t : ℕ))

theorem sqrt_W_pos (hρ : 0 < ρ) (t : ℕ) : 0 < Real.sqrt (W i j ρ t) :=
  Real.sqrt_pos.2 (W_pos hρ t)

theorem sqrt_W_ne_zero (hρ : 0 < ρ) (t : ℕ) : Real.sqrt (W i j ρ t) ≠ 0 :=
  ne_of_gt (sqrt_W_pos (i := i) (j := j) hρ t)

theorem phi_psi (hρ : 0 < ρ) (v : Fin (min i j + 1) → ℝ) : phi i j ρ (psi i j ρ v) = v := by
  funext t
  have h : Real.sqrt (W i j ρ (t : ℕ)) ≠ 0 := sqrt_W_ne_zero (i := i) (j := j) hρ _
  simp only [phi, psi]
  field_simp

theorem psi_phi (hρ : 0 < ρ) (u : Fin (min i j + 1) → ℝ) : psi i j ρ (phi i j ρ u) = u := by
  funext t
  have h : Real.sqrt (W i j ρ (t : ℕ)) ≠ 0 := sqrt_W_ne_zero (i := i) (j := j) hρ _
  simp only [phi, psi]
  field_simp

theorem phi_smul (c : ℝ) (u : Fin (min i j + 1) → ℝ) :
    phi i j ρ (c • u) = c • phi i j ρ u := by
  funext t
  simp only [phi, Pi.smul_apply, smul_eq_mul]
  ring

theorem phi_injective (hρ : 0 < ρ) : Function.Injective (phi i j ρ) := by
  intro u v huv
  have := congrArg (psi i j ρ) huv
  rwa [psi_phi hρ, psi_phi hρ] at this

theorem phi_ne_zero (hρ : 0 < ρ) {u : Fin (min i j + 1) → ℝ} (hu : u ≠ 0) : phi i j ρ u ≠ 0 := by
  intro hc
  refine hu (phi_injective (i := i) (j := j) hρ ?_)
  rw [hc]
  funext t
  simp [phi]

theorem psi_ne_zero (hρ : 0 < ρ) {v : Fin (min i j + 1) → ℝ} (hv : v ≠ 0) : psi i j ρ v ≠ 0 := by
  intro hc
  refine hv ?_
  rw [← phi_psi (i := i) (j := j) hρ v, hc]
  funext t
  simp [phi]

theorem phi_dotProduct (hρ : 0 < ρ) (u v : Fin (min i j + 1) → ℝ) :
    phi i j ρ u ⬝ᵥ phi i j ρ v = innerW i j ρ u v := by
  simp only [dotProduct, innerW, phi]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : Real.sqrt (W i j ρ (t : ℕ)) * Real.sqrt (W i j ρ (t : ℕ)) = W i j ρ (t : ℕ) :=
    Real.mul_self_sqrt (W_pos hρ _).le
  rw [div_mul_div_comm, h1]

theorem symT_mulVec_phi (hρ : 0 < ρ) (u : Fin (min i j + 1) → ℝ) :
    symT i j θA θB ρ *ᵥ phi i j ρ u = phi i j ρ (T i j θA θB ρ *ᵥ u) := by
  funext t
  simp only [phi, mulVec_apply]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hWs : 0 < W i j ρ (s : ℕ) := W_pos hρ _
  have h1 : Real.sqrt (W i j ρ (s : ℕ)) ≠ 0 := sqrt_W_ne_zero (i := i) (j := j) hρ _
  have h2 : Real.sqrt (W i j ρ (t : ℕ)) ≠ 0 := sqrt_W_ne_zero (i := i) (j := j) hρ _
  simp only [symT]
  rw [Real.sqrt_div hWs.le]
  field_simp

theorem mulVec_symT_iff (hρ : 0 < ρ) {ν : ℝ} (u : Fin (min i j + 1) → ℝ) :
    symT i j θA θB ρ *ᵥ phi i j ρ u = ν • phi i j ρ u ↔ T i j θA θB ρ *ᵥ u = ν • u := by
  rw [symT_mulVec_phi hρ, ← phi_smul]
  exact ⟨fun h => phi_injective (i := i) (j := j) hρ h, fun h => congrArg _ h⟩

theorem symT_isHermitian (hρ : 0 < ρ) : (symT i j θA θB ρ).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (symT_isSymm hρ)

end Rhone.LinearAlgebra.Spectral
