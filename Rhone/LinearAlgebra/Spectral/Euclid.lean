/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Witness
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Euclidean-norm decay at the spectral floor fails for an explicit `(1,1)` block -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset
open scoped Matrix.Norms.Operator

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def mulVecL (x : n → ℝ) : Matrix n n ℝ →ₗ[ℝ] (n → ℝ) where
  toFun := fun A => A *ᵥ x
  map_add' := fun A B => by simp [Matrix.add_mulVec]
  map_smul' := fun r A => by simp [Matrix.smul_mulVec]

theorem hasDerivAt_exp_mulVec (M : Matrix n n ℝ) (x : n → ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-M)) *ᵥ x) ((-M) *ᵥ x) 0 := by
  have hE : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-M)))
      (NormedSpace.exp ((0 : ℝ) • (-M)) * (-M)) 0 := hasDerivAt_exp_smul_const (-M) 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hE
  exact ((mulVecL x).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt 0 hE

theorem hasDerivAt_dotProduct_exp (M : Matrix n n ℝ) (x : n → ℝ) :
    HasDerivAt
      (fun s : ℝ => (NormedSpace.exp (s • (-M)) *ᵥ x) ⬝ᵥ (NormedSpace.exp (s • (-M)) *ᵥ x))
      (-2 * (x ⬝ᵥ (M *ᵥ x))) 0 := by
  have hv := hasDerivAt_exp_mulVec M x
  have hv0 : NormedSpace.exp ((0 : ℝ) • (-M)) *ᵥ x = x := by
    rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
  have hcomp : ∀ k : n, HasDerivAt
      (fun s : ℝ => (NormedSpace.exp (s • (-M)) *ᵥ x) k) (((-M) *ᵥ x) k) 0 :=
    fun k => hasDerivAt_pi.1 hv k
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ k ∈ (Finset.univ : Finset n), (NormedSpace.exp (s • (-M)) *ᵥ x) k
        * (NormedSpace.exp (s • (-M)) *ᵥ x) k)
      (∑ k ∈ (Finset.univ : Finset n), (((-M) *ᵥ x) k * x k + x k * ((-M) *ᵥ x) k)) 0 :=
    HasDerivAt.fun_sum (u := (Finset.univ : Finset n))
      (A := fun k (s : ℝ) => (NormedSpace.exp (s • (-M)) *ᵥ x) k
        * (NormedSpace.exp (s • (-M)) *ᵥ x) k)
      (A' := fun k => ((-M) *ᵥ x) k * x k + x k * ((-M) *ᵥ x) k)
      fun k _ => by
        have := (hcomp k).mul (hcomp k)
        rwa [hv0] at this
  have hval : (∑ k ∈ (Finset.univ : Finset n), (((-M) *ᵥ x) k * x k + x k * ((-M) *ᵥ x) k))
      = -2 * (x ⬝ᵥ (M *ᵥ x)) := by
    rw [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.neg_mulVec, Pi.neg_apply]
    ring
  rw [hval] at hsum
  exact hsum

end General

theorem eventually_pos_of_hasDerivAt_pos {H : ℝ → ℝ} {d : ℝ} (hH : HasDerivAt H d 0)
    (h0 : H 0 = 0) (hd : 0 < d) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < H s := by
  have hslope := hasDerivAt_iff_tendsto_slope.1 hH
  have hpos : ∀ᶠ s in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, 0 < slope H 0 s :=
    hslope.eventually (lt_mem_nhds hd)
  have hsub : Set.Ioi (0 : ℝ) ⊆ {(0 : ℝ)}ᶜ := fun y hy => ne_of_gt hy
  have hpos' : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < slope H 0 s :=
    hpos.filter_mono (nhdsWithin_mono 0 hsub)
  filter_upwards [hpos', self_mem_nhdsWithin] with s hs hs0
  have hs0' : (0 : ℝ) < s := hs0
  have hval : slope H 0 s = s⁻¹ * H s := by
    rw [slope_def_field, h0, sub_zero, sub_zero, div_eq_inv_mul]
  rw [hval] at hs
  have hid : H s = s * (s⁻¹ * H s) := by
    field_simp
  rw [hid]
  exact mul_pos hs0' hs

section Failure

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem euclidean_decay_false_of_rayleigh {A : Matrix n n ℝ} {x : n → ℝ} {μ : ℝ}
    (h : x ⬝ᵥ (A *ᵥ x) < μ * (x ⬝ᵥ x)) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Real.exp (-(s * μ)) ^ 2 * (x ⬝ᵥ x)
        < (NormedSpace.exp (s • (-A)) *ᵥ x) ⬝ᵥ (NormedSpace.exp (s • (-A)) *ᵥ x) := by
  simp only [pow_two]
  have hF := hasDerivAt_dotProduct_exp A x
  have hlin : HasDerivAt (fun s : ℝ => -(s * μ)) (-μ) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const μ).neg
    rw [one_mul] at h
    exact h
  have hG := (hlin.exp.mul hlin.exp).mul_const (x ⬝ᵥ x)
  have hz : Real.exp (-((0 : ℝ) * μ)) = 1 := by norm_num
  rw [hz] at hG
  have hd0 : ((1 : ℝ) * -μ * 1 + 1 * (1 * -μ)) * (x ⬝ᵥ x) = -(2 * μ) * (x ⬝ᵥ x) := by ring
  rw [hd0] at hG
  have hH := hF.sub hG
  have h0 : ((fun s : ℝ =>
        (NormedSpace.exp (s • (-A)) *ᵥ x) ⬝ᵥ (NormedSpace.exp (s • (-A)) *ᵥ x))
      - fun s : ℝ => Real.exp (-(s * μ)) * Real.exp (-(s * μ)) * (x ⬝ᵥ x)) 0 = 0 := by
    simp only [Pi.sub_apply, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
    norm_num
  have hd : 0 < -2 * (x ⬝ᵥ (A *ᵥ x)) - -(2 * μ) * (x ⬝ᵥ x) := by linarith
  have hev := eventually_pos_of_hasDerivAt_pos hH h0 hd
  filter_upwards [hev] with s hs
  simp only [Pi.sub_apply, Pi.mul_apply] at hs
  linarith

end Failure

theorem euclidean_decay_false_rho_pos :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      Real.exp (-(s * floorMu 1 1 2 3)) ^ 2
          * ((![10, 9] : Fin (min 1 1 + 1) → ℝ) ⬝ᵥ ![10, 9])
        < (NormedSpace.exp (s • (-Te 1 1 1 2 3 (5 / 2))) *ᵥ (![10, 9] : Fin (min 1 1 + 1) → ℝ))
            ⬝ᵥ (NormedSpace.exp (s • (-Te 1 1 1 2 3 (5 / 2))) *ᵥ ![10, 9]) := by
  rw [Te_lam_one]
  refine euclidean_decay_false_of_rayleigh ?_
  have hsym := euclidean_measure_fails_rho_pos
  have hsplit : (![10, 9] : Fin (min 1 1 + 1) → ℝ)
      ⬝ᵥ ((T 1 1 2 3 (5 / 2) + (T 1 1 2 3 (5 / 2))ᵀ) *ᵥ ![10, 9])
      = 2 * ((![10, 9] : Fin (min 1 1 + 1) → ℝ) ⬝ᵥ (T 1 1 2 3 (5 / 2) *ᵥ ![10, 9])) := by
    simp only [dotProduct_two, mulVec_two, Matrix.add_apply, Matrix.transpose_apply]
    ring
  rw [hsplit] at hsym
  linarith

theorem T11b_eigen_five :
    T 1 1 2 3 (5 / 2) *ᵥ (![1, 1] : Fin (min 1 1 + 1) → ℝ) = (5 : ℝ) • ![1, 1] := by
  funext t
  rw [mulVec_two]
  fin_cases t <;>
    norm_num [T11b_apply_zero_zero, T11b_apply_zero_one, T11b_apply_one_zero,
      T11b_apply_one_one, Tdiag, Tsup, Tsub]

theorem T11b_eigen_nineteen_half :
    T 1 1 2 3 (5 / 2) *ᵥ (![4, -5] : Fin (min 1 1 + 1) → ℝ) = (19 / 2 : ℝ) • ![4, -5] := by
  funext t
  rw [mulVec_two]
  fin_cases t <;>
    norm_num [T11b_apply_zero_zero, T11b_apply_zero_one, T11b_apply_one_zero,
      T11b_apply_one_one, Tdiag, Tsup, Tsub]

theorem exp_neg_T11b (s : ℝ) :
    NormedSpace.exp (s • (-T 1 1 2 3 (5 / 2))) *ᵥ (![10, 9] : Fin (min 1 1 + 1) → ℝ)
      = (86 / 9 * Real.exp (-(s * 5))) • (![1, 1] : Fin (min 1 1 + 1) → ℝ)
        + (1 / 9 * Real.exp (-(s * (19 / 2)))) • (![4, -5] : Fin (min 1 1 + 1) → ℝ) := by
  have hsplit : (![10, 9] : Fin (min 1 1 + 1) → ℝ)
      = (86 / 9 : ℝ) • (![1, 1] : Fin (min 1 1 + 1) → ℝ)
        + (1 / 9 : ℝ) • (![4, -5] : Fin (min 1 1 + 1) → ℝ) := by
    funext t; fin_cases t <;> norm_num
  have h1 : NormedSpace.exp (s • (-T 1 1 2 3 (5 / 2))) *ᵥ (![1, 1] : Fin (min 1 1 + 1) → ℝ)
      = Real.exp (-(s * 5)) • ![1, 1] := by
    refine exp_mulVec_of_eigen ?_
    rw [Matrix.smul_mulVec, Matrix.neg_mulVec, T11b_eigen_five, smul_neg, smul_smul, ← neg_smul]
  have h2 : NormedSpace.exp (s • (-T 1 1 2 3 (5 / 2))) *ᵥ (![4, -5] : Fin (min 1 1 + 1) → ℝ)
      = Real.exp (-(s * (19 / 2))) • ![4, -5] := by
    refine exp_mulVec_of_eigen ?_
    rw [Matrix.smul_mulVec, Matrix.neg_mulVec, T11b_eigen_nineteen_half, smul_neg, smul_smul,
      ← neg_smul]
  rw [hsplit, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, smul_smul,
    smul_smul]

theorem euclidean_decay_false_rho_pos_exact {s : ℝ} (hs : 0 < s) :
    Real.exp (-(s * floorMu 1 1 2 3)) ^ 2
        * ((![10, 9] : Fin (min 1 1 + 1) → ℝ) ⬝ᵥ ![10, 9])
      < (NormedSpace.exp (s • (-Te 1 1 1 2 3 (5 / 2))) *ᵥ (![10, 9] : Fin (min 1 1 + 1) → ℝ))
          ⬝ᵥ (NormedSpace.exp (s • (-Te 1 1 1 2 3 (5 / 2))) *ᵥ ![10, 9]) := by
  have hfloor : floorMu 1 1 2 3 = 5 := by unfold floorMu; norm_num
  rw [Te_lam_one, exp_neg_T11b, hfloor]
  set E := Real.exp (-(s * 5)) with hE
  set w := Real.exp (-(s * (9 / 2))) with hW
  have hEpos : 0 < E := Real.exp_pos _
  have hwpos : 0 < w := Real.exp_pos _
  have hw1 : w < 1 := by
    rw [hW]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have hmix : Real.exp (-(s * (19 / 2))) = E * w := by
    rw [hE, hW, ← Real.exp_add]
    ring_nf
  rw [hmix]
  have hx : (![10, 9] : Fin (min 1 1 + 1) → ℝ) ⬝ᵥ ![10, 9] = 181 := by
    rw [dotProduct_two]; norm_num
  rw [hx, dotProduct_two]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  nlinarith [hEpos, hwpos, hw1, sq_nonneg E, sq_nonneg w, mul_pos hEpos hEpos,
    mul_pos (mul_pos hEpos hEpos) (mul_pos (sub_pos.2 hw1) (by linarith : (0:ℝ) < 131 - 41 * w))]

end Rhone.LinearAlgebra.Spectral
