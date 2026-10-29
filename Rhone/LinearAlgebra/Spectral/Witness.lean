/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Contraction

/-! # The Euclidean version of the decay bound is false -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset

theorem W_eq_zero_of_rho_zero (i j : ℕ) {t : ℕ} (ht : 1 ≤ t) : W i j 0 t = 0 := by
  unfold W
  rw [zero_pow (by omega)]
  simp

theorem innerW_rho_zero_not_definite {i j : ℕ} (h : 1 ≤ min i j) :
    ∃ u : Fin (min i j + 1) → ℝ, u ≠ 0 ∧ innerW i j 0 u u = 0 := by
  classical
  refine ⟨Pi.single ⟨1, Nat.lt_succ_of_le h⟩ 1, ?_, ?_⟩
  · intro hc
    have := congrFun hc (⟨1, Nat.lt_succ_of_le h⟩ : Fin (min i j + 1))
    simp at this
  · unfold innerW
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t = (⟨1, Nat.lt_succ_of_le h⟩ : Fin (min i j + 1))
    · subst ht
      have h1 : W i j 0 ((⟨1, Nat.lt_succ_of_le h⟩ : Fin (min i j + 1)) : ℕ) = 0 :=
        W_eq_zero_of_rho_zero i j (le_refl 1)
      rw [h1]
      simp
    · rw [Pi.single_eq_of_ne ht]
      simp

theorem dotProduct_two (u v : Fin (min 1 1 + 1) → ℝ) : u ⬝ᵥ v = u 0 * v 0 + u 1 * v 1 :=
  Fin.sum_univ_two _

theorem mulVec_two (M : Matrix (Fin (min 1 1 + 1)) (Fin (min 1 1 + 1)) ℝ)
    (v : Fin (min 1 1 + 1) → ℝ) (t : Fin (min 1 1 + 1)) :
    (M *ᵥ v) t = M t 0 * v 0 + M t 1 * v 1 := by
  rw [mulVec_apply]
  exact Fin.sum_univ_two _

theorem Te_lam_one (i j : ℕ) (θA θB ρ : ℝ) : Te i j 1 θA θB ρ = T i j θA θB ρ := by
  unfold Te
  rw [inv_one, one_smul, one_mul, one_mul, one_mul]

theorem T11_apply_zero_zero : T 1 1 1 1 0 0 0 = 4 := by
  rw [T_apply_diag]; unfold Tdiag; norm_num

theorem T11_apply_zero_one : T 1 1 1 1 0 0 1 = -2 := by
  rw [T_apply_sup (by decide)]; unfold Tsup; norm_num

theorem T11_apply_one_zero : T 1 1 1 1 0 1 0 = 0 := by
  rw [T_apply_sub (by decide)]; unfold Tsub; norm_num

theorem T11_apply_one_one : T 1 1 1 1 0 1 1 = 2 := by
  rw [T_apply_diag]; unfold Tdiag; norm_num

theorem T11_eigen_four :
    T 1 1 1 1 0 *ᵥ (![1, 0] : Fin (min 1 1 + 1) → ℝ) = (4 : ℝ) • ![1, 0] := by
  funext t
  rw [mulVec_two]
  fin_cases t <;>
    norm_num [T11_apply_zero_zero, T11_apply_zero_one, T11_apply_one_zero, T11_apply_one_one,
      Tdiag, Tsup, Tsub]

theorem T11_eigen_two :
    T 1 1 1 1 0 *ᵥ (![1, 1] : Fin (min 1 1 + 1) → ℝ) = (2 : ℝ) • ![1, 1] := by
  funext t
  rw [mulVec_two]
  fin_cases t <;>
    norm_num [T11_apply_zero_zero, T11_apply_zero_one, T11_apply_one_zero, T11_apply_one_one,
      Tdiag, Tsup, Tsub]

theorem floorMu_one_one : floorMu 1 1 1 1 = 2 := by
  unfold floorMu; norm_num

theorem exp_neg_T11_e_one (s : ℝ) :
    NormedSpace.exp (s • (-T 1 1 1 1 0)) *ᵥ (![0, 1] : Fin (min 1 1 + 1) → ℝ)
      = Real.exp (-(s * 2)) • ![1, 1] - Real.exp (-(s * 4)) • ![1, 0] := by
  have hsplit : (![0, 1] : Fin (min 1 1 + 1) → ℝ)
      = (![1, 1] : Fin (min 1 1 + 1) → ℝ) - (![1, 0] : Fin (min 1 1 + 1) → ℝ) := by
    funext t; fin_cases t <;> norm_num
  have h2 : NormedSpace.exp (s • (-T 1 1 1 1 0)) *ᵥ (![1, 1] : Fin (min 1 1 + 1) → ℝ)
      = Real.exp (-(s * 2)) • ![1, 1] := by
    refine exp_mulVec_of_eigen ?_
    rw [Matrix.smul_mulVec, Matrix.neg_mulVec, T11_eigen_two, smul_neg, smul_smul, ← neg_smul]
  have h4 : NormedSpace.exp (s • (-T 1 1 1 1 0)) *ᵥ (![1, 0] : Fin (min 1 1 + 1) → ℝ)
      = Real.exp (-(s * 4)) • ![1, 0] := by
    refine exp_mulVec_of_eigen ?_
    rw [Matrix.smul_mulVec, Matrix.neg_mulVec, T11_eigen_four, smul_neg, smul_smul, ← neg_smul]
  rw [hsplit, Matrix.mulVec_sub, h2, h4]

theorem euclidean_decay_false_at_block_one_one {s : ℝ} (hs : 0 < s) :
    Real.exp (-(s * floorMu 1 1 1 1)) ^ 2
        * ((![0, 1] : Fin (min 1 1 + 1) → ℝ) ⬝ᵥ ![0, 1])
      < (NormedSpace.exp (s • (-Te 1 1 1 1 1 0)) *ᵥ (![0, 1] : Fin (min 1 1 + 1) → ℝ))
          ⬝ᵥ (NormedSpace.exp (s • (-Te 1 1 1 1 1 0)) *ᵥ ![0, 1]) := by
  rw [Te_lam_one, exp_neg_T11_e_one, floorMu_one_one]
  have hne : Real.exp (-(s * 4)) < Real.exp (-(s * 2)) := Real.exp_lt_exp.2 (by linarith)
  have hval : (Real.exp (-(s * 2)) • (![1, 1] : Fin (min 1 1 + 1) → ℝ)
        - Real.exp (-(s * 4)) • ![1, 0])
      ⬝ᵥ (Real.exp (-(s * 2)) • (![1, 1] : Fin (min 1 1 + 1) → ℝ)
        - Real.exp (-(s * 4)) • ![1, 0])
      = (Real.exp (-(s * 2)) - Real.exp (-(s * 4))) ^ 2 + Real.exp (-(s * 2)) ^ 2 := by
    rw [dotProduct_two]
    norm_num
    ring
  rw [hval]
  have hx : (![0, 1] : Fin (min 1 1 + 1) → ℝ) ⬝ᵥ ![0, 1] = 1 := by
    rw [dotProduct_two]; norm_num
  rw [hx, mul_one]
  have hgap : 0 < (Real.exp (-(s * 2)) - Real.exp (-(s * 4))) ^ 2 := by
    have : Real.exp (-(s * 2)) - Real.exp (-(s * 4)) ≠ 0 := by linarith
    positivity
  linarith [hgap]

theorem T11b_apply_zero_zero : T 1 1 2 3 (5 / 2) 0 0 = 7 := by
  rw [T_apply_diag]; unfold Tdiag; norm_num

theorem T11b_apply_zero_one : T 1 1 2 3 (5 / 2) 0 1 = -2 := by
  rw [T_apply_sup (by decide)]; unfold Tsup; norm_num

theorem T11b_apply_one_zero : T 1 1 2 3 (5 / 2) 1 0 = -(5 / 2) := by
  rw [T_apply_sub (by decide)]; unfold Tsub; norm_num

theorem T11b_apply_one_one : T 1 1 2 3 (5 / 2) 1 1 = 15 / 2 := by
  rw [T_apply_diag]; unfold Tdiag; norm_num

theorem euclidean_measure_fails_rho_pos :
    (![10, 9] : Fin (min 1 1 + 1) → ℝ)
        ⬝ᵥ ((T 1 1 2 3 (5 / 2) + (T 1 1 2 3 (5 / 2))ᵀ) *ᵥ ![10, 9])
      < 2 * floorMu 1 1 2 3 * ((![10, 9] : Fin (min 1 1 + 1) → ℝ) ⬝ᵥ ![10, 9]) := by
  have hfloor : floorMu 1 1 2 3 = 5 := by unfold floorMu; norm_num
  rw [hfloor, dotProduct_two, dotProduct_two, mulVec_two, mulVec_two]
  simp only [Matrix.add_apply, Matrix.transpose_apply, T11b_apply_zero_zero,
    T11b_apply_zero_one, T11b_apply_one_zero, T11b_apply_one_one]
  norm_num

end Rhone.LinearAlgebra.Spectral
