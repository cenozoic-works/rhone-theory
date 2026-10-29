/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Floor
public import Rhone.LinearAlgebra.Spectral.SelfAdjoint
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Sharp lower bound for the spectrum of the block operator, attained at `ρ = 0` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Finset
open scoped Matrix

variable {i j : ℕ} {θA θB ρ lam : ℝ}

theorem slack_row_le_bigS (t : Fin (min i j + 1)) :
    slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) ≤ bigS (i : ℝ) (j : ℝ) := by
  have hz := slack_le_bigS (i := (i : ℤ)) (j := (j : ℤ)) (t := ((t : ℕ) : ℤ))
    (Int.natCast_nonneg _)
  have hcast : ((slack (i : ℤ) (j : ℤ) ((t : ℕ) : ℤ) : ℤ) : ℝ)
      ≤ ((bigS (i : ℤ) (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast hz
  rwa [slack_intCast, bigS_intCast] at hcast

theorem T_mulVec_one (t : Fin (min i j + 1)) :
    (T i j θA θB ρ *ᵥ fun _ => (1 : ℝ)) t
      = floorMu i j θA θB + slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) := by
  rw [mulVec_apply]
  simp only [mul_one]
  rw [T_row_sum]
  unfold floorMu
  ring

theorem innerW_one_T_one_eq :
    innerW i j ρ (T i j θA θB ρ *ᵥ fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      = ∑ t : Fin (min i j + 1),
          (floorMu i j θA θB + slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ)) / W i j ρ (t : ℕ) := by
  unfold innerW
  exact Finset.sum_congr rfl fun t _ => by rw [T_mulVec_one, mul_one]

theorem innerW_one_T_one_le (hρ : 0 < ρ) :
    innerW i j ρ (T i j θA θB ρ *ᵥ fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      ≤ (floorMu i j θA θB + bigS (i : ℝ) (j : ℝ))
          * innerW i j ρ (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  rw [innerW_one_T_one_eq]
  unfold innerW
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hW : 0 < W i j ρ (t : ℕ) := W_pos hρ _
  have hs := slack_row_le_bigS (i := i) (j := j) t
  rw [one_mul, mul_one_div]
  gcongr

theorem innerW_one_T_one_ge (hρ : 0 < ρ) :
    (floorMu i j θA θB
        + (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)))
        * innerW i j ρ (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      ≤ innerW i j ρ (T i j θA θB ρ *ᵥ fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
  rw [innerW_one_T_one_eq]
  unfold innerW
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hW : 0 < W i j ρ (t : ℕ) := W_pos hρ _
  have hs := slack_row_ge_min (i := i) (j := j) t
  rw [one_mul, mul_one_div]
  gcongr

theorem Tdiag_min_eq :
    Tdiag i j θA θB 0 (min i j)
      = floorMu i j θA θB
        + (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) := by
  unfold Tdiag floorMu bigS
  rcases le_total i j with h | h
  · rw [min_eq_left h]; ring
  · rw [min_eq_right h]; ring

theorem exists_eigenvector_rho_zero :
    ∃ v : Fin (min i j + 1) → ℝ, v ≠ 0 ∧
      T i j θA θB 0 *ᵥ v
        = (floorMu i j θA θB
            + (bigS (i : ℝ) (j : ℝ)
              - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1))) • v := by
  set c : ℝ := floorMu i j θA θB
      + (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) with hc
  have hdet : (T i j θA θB 0
      - Matrix.diagonal (fun _ : Fin (min i j + 1) => c)).det = 0 := by
    rw [det_sub_smul_one_of_rho_zero]
    refine Finset.prod_eq_zero
      (Finset.mem_univ (⟨min i j, Nat.lt_succ_self _⟩ : Fin (min i j + 1))) ?_
    change Tdiag i j θA θB 0 (min i j) - c = 0
    rw [Tdiag_min_eq, hc, sub_self]
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_⟩
  have hd : (Matrix.diagonal (fun _ : Fin (min i j + 1) => c)) *ᵥ v = c • v := by
    funext t
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [Matrix.sub_mulVec, hd, sub_eq_zero] at hvz
  exact hvz

theorem Te_exists_eigenvector_rho_zero (hlam : 0 < lam) :
    ∃ v : Fin (min i j + 1) → ℝ, v ≠ 0 ∧
      Te i j lam θA θB 0 *ᵥ v
        = (floorMu i j θA θB
            + (bigS (i : ℝ) (j : ℝ)
              - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam) • v := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  obtain ⟨v, hv, hveq⟩ := exists_eigenvector_rho_zero (i := i) (j := j)
    (θA := lam * θA) (θB := lam * θB)
  refine ⟨v, hv, ?_⟩
  have hzero : lam * (0 : ℝ) = 0 := by ring
  rw [Te_mulVec_iff hlam']
  rw [hzero]
  rw [hveq]
  congr 1
  unfold floorMu
  field_simp

theorem block_one_one_floor_attained (a b r : ℝ) :
    ∃ v : Fin (min 1 1 + 1) → ℝ, v ≠ 0 ∧
      T 1 1 a b r *ᵥ v = floorMu 1 1 a b • v := by
  have hdet : (T 1 1 a b r
      - Matrix.diagonal (fun _ : Fin (min 1 1 + 1) => floorMu 1 1 a b)).det = 0 := by
    have h00 : (T 1 1 a b r
        - Matrix.diagonal (fun _ : Fin (min 1 1 + 1) => floorMu 1 1 a b)) 0 0 = 2 := by
      rw [Matrix.sub_apply, T_apply_diag, Matrix.diagonal_apply_eq]
      unfold Tdiag floorMu
      norm_num
    have h01 : (T 1 1 a b r
        - Matrix.diagonal (fun _ : Fin (min 1 1 + 1) => floorMu 1 1 a b)) 0 1 = -2 := by
      rw [Matrix.sub_apply, T_apply_sup (by decide), Matrix.diagonal_apply_ne _ (by decide)]
      unfold Tsup
      norm_num
    have h10 : (T 1 1 a b r
        - Matrix.diagonal (fun _ : Fin (min 1 1 + 1) => floorMu 1 1 a b)) 1 0 = -r := by
      rw [Matrix.sub_apply, T_apply_sub (by decide), Matrix.diagonal_apply_ne _ (by decide)]
      unfold Tsub
      norm_num
    have h11 : (T 1 1 a b r
        - Matrix.diagonal (fun _ : Fin (min 1 1 + 1) => floorMu 1 1 a b)) 1 1 = r := by
      rw [Matrix.sub_apply, T_apply_diag, Matrix.diagonal_apply_eq]
      unfold Tdiag floorMu
      norm_num
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_⟩
  have hd : (Matrix.diagonal (fun _ : Fin (min 1 1 + 1) => floorMu 1 1 a b)) *ᵥ v
      = floorMu 1 1 a b • v := by
    funext t
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [Matrix.sub_mulVec, hd, sub_eq_zero] at hvz
  exact hvz

end Rhone.LinearAlgebra.Spectral
