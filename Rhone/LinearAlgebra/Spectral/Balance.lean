/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Detailed balance of every epoch operator with respect to the weights `W` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Finset
open scoped Matrix

noncomputable def W (i j : ℕ) (x : ℝ) (t : ℕ) : ℝ :=
  x ^ t * ((Nat.factorial t : ℝ) * (Nat.factorial (i - t) : ℝ) * (Nat.factorial (j - t) : ℝ))
    / (2 ^ t * (Nat.factorial i : ℝ) * (Nat.factorial j : ℝ))

variable {i j : ℕ} {x θA θB ρ : ℝ}

theorem factorial_cast_ne_zero (n : ℕ) : (Nat.factorial n : ℝ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

@[simp] theorem W_zero : W i j x 0 = 1 := by
  have h5 : (Nat.factorial i : ℝ) ≠ 0 := factorial_cast_ne_zero i
  have h6 : (Nat.factorial j : ℝ) ≠ 0 := factorial_cast_ne_zero j
  unfold W
  simp only [pow_zero, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  field_simp

theorem W_pos (hx : 0 < x) (t : ℕ) : 0 < W i j x t := by
  unfold W
  have h1 : (0 : ℝ) < x ^ t := pow_pos hx t
  have h2 : (0 : ℝ) < (Nat.factorial t : ℝ) := by exact_mod_cast Nat.factorial_pos t
  have h3 : (0 : ℝ) < (Nat.factorial (i - t) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h4 : (0 : ℝ) < (Nat.factorial (j - t) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h5 : (0 : ℝ) < (Nat.factorial i : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have h6 : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  positivity

theorem W_ratio {t : ℕ} (hti : t + 1 ≤ i) (htj : t + 1 ≤ j) :
    x * ((t : ℝ) + 1) * W i j x t
      = 2 * ((i : ℝ) - (t : ℝ)) * ((j : ℝ) - (t : ℝ)) * W i j x (t + 1) := by
  have hi : i - t = (i - (t + 1)) + 1 := by omega
  have hj : j - t = (j - (t + 1)) + 1 := by omega
  have hic : ((i - (t + 1) : ℕ) : ℝ) + 1 = (i : ℝ) - (t : ℝ) := by
    have h : ((i - (t + 1) : ℕ) : ℝ) = (i : ℝ) - ((t : ℝ) + 1) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h]; ring
  have hjc : ((j - (t + 1) : ℕ) : ℝ) + 1 = (j : ℝ) - (t : ℝ) := by
    have h : ((j - (t + 1) : ℕ) : ℝ) = (j : ℝ) - ((t : ℝ) + 1) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h]; ring
  unfold W
  rw [hi, hj]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [← hic, ← hjc]
  have e1 : (Nat.factorial i : ℝ) ≠ 0 := factorial_cast_ne_zero i
  have e2 : (Nat.factorial j : ℝ) ≠ 0 := factorial_cast_ne_zero j
  have e3 : (2 : ℝ) ^ t ≠ 0 := by positivity
  field_simp

theorem detailed_balance_succ {t s : Fin (min i j + 1)} (h : (s : ℕ) = (t : ℕ) + 1) :
    T i j θA θB ρ t s * W i j ρ (s : ℕ) = T i j θA θB ρ s t * W i j ρ (t : ℕ) := by
  have hs : (s : ℕ) ≤ min i j := by have := s.isLt; omega
  have hti : (t : ℕ) + 1 ≤ i := by omega
  have htj : (t : ℕ) + 1 ≤ j := by omega
  rw [T_apply_sup h, T_apply_sub (t := s) (s := t) h, h]
  unfold Tsup Tsub
  have hr := W_ratio (i := i) (j := j) (x := ρ) (t := (t : ℕ)) hti htj
  push_cast
  linear_combination hr

theorem detailed_balance (t s : Fin (min i j + 1)) :
    T i j θA θB ρ t s * W i j ρ (s : ℕ) = T i j θA θB ρ s t * W i j ρ (t : ℕ) := by
  by_cases hts : (s : ℕ) = (t : ℕ)
  · have hst : s = t := Fin.ext hts
    rw [hst]
  · by_cases h1 : (s : ℕ) = (t : ℕ) + 1
    · exact detailed_balance_succ h1
    · by_cases h2 : (t : ℕ) = (s : ℕ) + 1
      · exact (detailed_balance_succ h2).symm
      · rw [T_apply_zero hts h1 h2,
          T_apply_zero (fun hc => hts hc.symm) (by omega) (by omega)]
        ring

noncomputable def diagW (i j : ℕ) (x : ℝ) :
    Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) ℝ :=
  Matrix.diagonal fun t => W i j x (t : ℕ)

theorem T_mul_diagW : T i j θA θB ρ * diagW i j ρ = diagW i j ρ * (T i j θA θB ρ)ᵀ := by
  ext t s
  rw [diagW, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
    detailed_balance t s, mul_comm]

theorem diagW_inv_mul_mul_diagW (hρ : 0 < ρ) :
    Matrix.diagonal (fun t : Fin (min i j + 1) => (W i j ρ (t : ℕ))⁻¹)
        * T i j θA θB ρ * diagW i j ρ = (T i j θA θB ρ)ᵀ := by
  ext t s
  rw [diagW, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have hW : W i j ρ (t : ℕ) ≠ 0 := ne_of_gt (W_pos hρ _)
  have hdb := detailed_balance (i := i) (j := j) (θA := θA) (θB := θB) (ρ := ρ) t s
  field_simp
  linear_combination hdb

theorem Te_detailed_balance {lam : ℝ} (t s : Fin (min i j + 1)) :
    Te i j lam θA θB ρ t s * W i j (lam * ρ) (s : ℕ)
      = Te i j lam θA θB ρ s t * W i j (lam * ρ) (t : ℕ) := by
  unfold Te
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc, mul_assoc,
    detailed_balance t s]

theorem T_isUpperTriangular_of_rho_zero :
    (T i j θA θB 0).IsUpperTriangular := by
  intro t s h
  simp only [id] at h
  have hlt : (s : ℕ) < (t : ℕ) := h
  by_cases h2 : (t : ℕ) = (s : ℕ) + 1
  · rw [T_apply_sub h2]
    unfold Tsub
    ring
  · rw [T_apply_zero (by omega) (by omega) h2]

theorem det_sub_smul_one_of_rho_zero (c : ℝ) :
    (T i j θA θB 0 - Matrix.diagonal (fun _ : Fin (min i j + 1) => c)).det
      = ∏ t : Fin (min i j + 1), (Tdiag i j θA θB 0 (t : ℕ) - c) := by
  have htri : (T i j θA θB 0
      - Matrix.diagonal (fun _ : Fin (min i j + 1) => c)).IsUpperTriangular := by
    intro t s h
    have := T_isUpperTriangular_of_rho_zero (i := i) (j := j) (θA := θA) (θB := θB) h
    have hne : t ≠ s := by
      intro hc; rw [hc] at h; exact lt_irrefl _ h
    simp [Matrix.sub_apply, this, Matrix.diagonal_apply_ne _ hne]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp [Matrix.sub_apply, T_apply_diag]

end Rhone.LinearAlgebra.Spectral
