/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.EigenBasis
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Per-block homogeneous decay in the `W`-metric for the epoch generator (`ρ_e > 0`) -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset
open scoped Matrix.Norms.Operator Nat

section GeneralExp

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem pow_mulVec_of_eigen {M : Matrix n n ℝ} {ν : ℝ} {v : n → ℝ} (h : M *ᵥ v = ν • v)
    (k : ℕ) : M ^ k *ᵥ v = ν ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
    ring_nf

theorem exp_mulVec_of_eigen {M : Matrix n n ℝ} {ν : ℝ} {v : n → ℝ} (h : M *ᵥ v = ν • v) :
    (NormedSpace.exp M) *ᵥ v = Real.exp ν • v := by
  have hS : HasSum (fun k : ℕ => ((k ! : ℝ)⁻¹ : ℝ) • M ^ k) (NormedSpace.exp M) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M
  let L : Matrix n n ℝ →ₗ[ℝ] (n → ℝ) :=
    { toFun := fun A => A *ᵥ v
      map_add' := fun A B => by simp [Matrix.add_mulVec]
      map_smul' := fun r A => by simp [Matrix.smul_mulVec] }
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  have hterm : ∀ k : ℕ, L (((k ! : ℝ)⁻¹ : ℝ) • M ^ k) = (((k ! : ℝ)⁻¹ : ℝ) * ν ^ k) • v := by
    intro k
    change (((k ! : ℝ)⁻¹ : ℝ) • M ^ k) *ᵥ v = _
    rw [Matrix.smul_mulVec, pow_mulVec_of_eigen h k, smul_smul]
  have hmap : HasSum (fun k : ℕ => (((k ! : ℝ)⁻¹ : ℝ) * ν ^ k) • v) (L (NormedSpace.exp M)) := by
    have hraw := hS.map L.toAddMonoidHom hcont
    simpa [Function.comp_def, hterm] using hraw
  have hLexp : L (NormedSpace.exp M) = (NormedSpace.exp M) *ᵥ v := rfl
  rw [hLexp] at hmap
  have hR : HasSum (fun k : ℕ => ((k ! : ℝ)⁻¹ : ℝ) • ν ^ k) (Real.exp ν) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ν
  exact hmap.unique (by simpa [smul_eq_mul] using hR.smul_const v)

end GeneralExp

variable {i j : ℕ} {θA θB ρ lam : ℝ}

theorem innerW_smul_right (x : ℝ) (u v : Fin (min i j + 1) → ℝ) (c : ℝ) :
    innerW i j x u (c • v) = c * innerW i j x u v := by
  unfold innerW
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem innerW_sum_right {ι : Type*} (x : ℝ) (u : Fin (min i j + 1) → ℝ)
    (s : Finset ι) (f : ι → Fin (min i j + 1) → ℝ) :
    innerW i j x u (∑ k ∈ s, f k) = ∑ k ∈ s, innerW i j x u (f k) := by
  unfold innerW
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_apply, Finset.mul_sum, Finset.sum_div]

noncomputable def eigTe (i j : ℕ) (θA θB : ℝ) {lam ρ : ℝ} (hlam : 0 < lam) (hρ : 0 < ρ)
    (k : Fin (min i j + 1)) : Fin (min i j + 1) → ℝ :=
  eigW i j (lam * θA) (lam * θB) (mul_pos hlam hρ) k

noncomputable def eigTeval (i j : ℕ) (θA θB : ℝ) {lam ρ : ℝ} (hlam : 0 < lam) (hρ : 0 < ρ)
    (k : Fin (min i j + 1)) : ℝ :=
  eigWval i j (lam * θA) (lam * θB) (mul_pos hlam hρ) k / lam

theorem mulVec_eigTe (hlam : 0 < lam) (hρ : 0 < ρ) (k : Fin (min i j + 1)) :
    Te i j lam θA θB ρ *ᵥ eigTe i j θA θB hlam hρ k
      = eigTeval i j θA θB hlam hρ k • eigTe i j θA θB hlam hρ k := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  rw [Te_mulVec_iff hlam', eigTeval, mul_div_cancel₀ _ hlam']
  exact mulVec_eigW (mul_pos hlam hρ) k

theorem eigTeval_ge_floor (hlam : 0 < lam) (hρ : 0 < ρ) (k : Fin (min i j + 1)) :
    floorMu i j θA θB ≤ eigTeval i j θA θB hlam hρ k :=
  Te_eigen_ge_floor hlam hρ.le (eigW_ne_zero (mul_pos hlam hρ) k) (mulVec_eigTe hlam hρ k)

theorem innerW_eigTe (hlam : 0 < lam) (hρ : 0 < ρ) (k l : Fin (min i j + 1)) :
    innerW i j (lam * ρ) (eigTe i j θA θB hlam hρ k) (eigTe i j θA θB hlam hρ l)
      = if k = l then 1 else 0 :=
  innerW_eigW (mul_pos hlam hρ) k l

theorem eigTe_sum_repr (hlam : 0 < lam) (hρ : 0 < ρ) (u : Fin (min i j + 1) → ℝ) :
    ∑ k, innerW i j (lam * ρ) (eigTe i j θA θB hlam hρ k) u • eigTe i j θA θB hlam hρ k = u :=
  eigW_sum_repr (mul_pos hlam hρ) u

theorem innerW_sum_smul_eigW (hρ : 0 < ρ) (d : Fin (min i j + 1) → ℝ) :
    innerW i j ρ (∑ k, d k • eigW i j θA θB hρ k) (∑ k, d k • eigW i j θA θB hρ k)
      = ∑ k, d k ^ 2 := by
  have hcoef : ∀ l, innerW i j ρ (eigW i j θA θB hρ l) (∑ k, d k • eigW i j θA θB hρ k) = d l := by
    intro l
    rw [innerW_sum_right]
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (min i j + 1))),
        innerW i j ρ (eigW i j θA θB hρ l) (d k • eigW i j θA θB hρ k)
          = if l = k then d k else 0 := by
      intro k _
      rw [innerW_smul_right, innerW_eigW hρ l k]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq Finset.univ l d,
      ite_eq_left (Finset.mem_univ l)]
  rw [← innerW_expansion (i := i) (j := j) (θA := θA) (θB := θB) hρ]
  exact Finset.sum_congr rfl fun l _ => by rw [hcoef l, sq]

theorem innerW_sum_smul_eigTe (hlam : 0 < lam) (hρ : 0 < ρ) (d : Fin (min i j + 1) → ℝ) :
    innerW i j (lam * ρ) (∑ k, d k • eigTe i j θA θB hlam hρ k)
        (∑ k, d k • eigTe i j θA θB hlam hρ k)
      = ∑ k, d k ^ 2 :=
  innerW_sum_smul_eigW (mul_pos hlam hρ) d

theorem exp_mulVec_eigTe (hlam : 0 < lam) (hρ : 0 < ρ) (s : ℝ) (k : Fin (min i j + 1)) :
    NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ eigTe i j θA θB hlam hρ k
      = Real.exp (-(s * eigTeval i j θA θB hlam hρ k)) • eigTe i j θA θB hlam hρ k := by
  refine exp_mulVec_of_eigen ?_
  rw [Matrix.smul_mulVec, Matrix.neg_mulVec, mulVec_eigTe hlam hρ k, smul_neg, smul_smul,
    ← neg_smul]

theorem innerW_exp_neg_smul_Te_le_of_forall (hlam : 0 < lam) (hρ : 0 < ρ) {s c : ℝ}
    (hs : 0 ≤ s) (hc : ∀ k, c ≤ eigTeval i j θA θB hlam hρ k)
    (x : Fin (min i j + 1) → ℝ) :
    innerW i j (lam * ρ) (NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ x)
        (NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ x)
      ≤ Real.exp (-(s * c)) ^ 2 * innerW i j (lam * ρ) x x := by
  classical
  have hx : ∑ k, innerW i j (lam * ρ) (eigTe i j θA θB hlam hρ k) x
      • eigTe i j θA θB hlam hρ k = x := eigTe_sum_repr hlam hρ x
  have hFx : NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ x
      = ∑ k, (innerW i j (lam * ρ) (eigTe i j θA θB hlam hρ k) x
          * Real.exp (-(s * eigTeval i j θA θB hlam hρ k))) • eigTe i j θA θB hlam hρ k := by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_smul, exp_mulVec_eigTe hlam hρ s k, smul_smul]
  have hrhs : innerW i j (lam * ρ) x x
      = ∑ k, (innerW i j (lam * ρ) (eigTe i j θA θB hlam hρ k) x) ^ 2 := by
    rw [← innerW_expansion (i := i) (j := j) (θA := lam * θA) (θB := lam * θB)
      (mul_pos hlam hρ) x x]
    exact Finset.sum_congr rfl fun k _ => (sq _).symm
  rw [hFx, innerW_sum_smul_eigTe hlam hρ, hrhs, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  set A := innerW i j (lam * ρ) (eigTe i j θA θB hlam hρ k) x with hA
  have hexp : Real.exp (-(s * eigTeval i j θA θB hlam hρ k)) ≤ Real.exp (-(s * c)) :=
    Real.exp_le_exp.2 (by nlinarith [hc k])
  have hpos : 0 < Real.exp (-(s * eigTeval i j θA θB hlam hρ k)) := Real.exp_pos _
  have hsq : Real.exp (-(s * eigTeval i j θA θB hlam hρ k)) ^ 2 ≤ Real.exp (-(s * c)) ^ 2 := by
    nlinarith [hpos, hexp]
  calc (A * Real.exp (-(s * eigTeval i j θA θB hlam hρ k))) ^ 2
      = A ^ 2 * Real.exp (-(s * eigTeval i j θA θB hlam hρ k)) ^ 2 := by ring
    _ ≤ A ^ 2 * Real.exp (-(s * c)) ^ 2 := by nlinarith [sq_nonneg A, hsq]
    _ = Real.exp (-(s * c)) ^ 2 * A ^ 2 := by ring

theorem innerW_exp_neg_smul_Te_le_floor (hlam : 0 < lam) (hρ : 0 < ρ) {s : ℝ} (hs : 0 ≤ s)
    (x : Fin (min i j + 1) → ℝ) :
    innerW i j (lam * ρ) (NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ x)
        (NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ x)
      ≤ Real.exp (-(s * floorMu i j θA θB)) ^ 2 * innerW i j (lam * ρ) x x :=
  innerW_exp_neg_smul_Te_le_of_forall hlam hρ hs (eigTeval_ge_floor hlam hρ) x

theorem innerW_exp_neg_smul_Te_le_lambdaMin (hlam : 0 < lam) (hρ : 0 < ρ) {s c : ℝ}
    (hs : 0 ≤ s) (hc : IsLeast (TeSpec i j lam θA θB ρ) c)
    (x : Fin (min i j + 1) → ℝ) :
    innerW i j (lam * ρ) (NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ x)
        (NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ x)
      ≤ Real.exp (-(s * c)) ^ 2 * innerW i j (lam * ρ) x x := by
  refine innerW_exp_neg_smul_Te_le_of_forall hlam hρ hs (fun k => ?_) x
  exact hc.2 ⟨eigTe i j θA θB hlam hρ k, eigW_ne_zero (mul_pos hlam hρ) k,
    mulVec_eigTe hlam hρ k⟩

theorem innerW_exp_neg_smul_Te_eq_at_eigenvector {s c : ℝ}
    {v : Fin (min i j + 1) → ℝ} (hveq : Te i j lam θA θB ρ *ᵥ v = c • v) :
    innerW i j (lam * ρ) (NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ v)
        (NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ v)
      = Real.exp (-(s * c)) ^ 2 * innerW i j (lam * ρ) v v := by
  have hFv : NormedSpace.exp (s • (-Te i j lam θA θB ρ)) *ᵥ v = Real.exp (-(s * c)) • v := by
    refine exp_mulVec_of_eigen ?_
    rw [Matrix.smul_mulVec, Matrix.neg_mulVec, hveq, smul_neg, smul_smul, ← neg_smul]
  rw [hFv, innerW_comm, innerW_smul_right, innerW_comm, innerW_smul_right, sq]
  ring

end Rhone.LinearAlgebra.Spectral
