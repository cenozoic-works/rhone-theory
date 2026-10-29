/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Defs
public import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! # The `λ`-uniform spectral floor for eigenvalues of the block and epoch operators -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Finset
open scoped Matrix

noncomputable def floorMu (i j : ℕ) (θA θB : ℝ) : ℝ := (i : ℝ) * θA + (j : ℝ) * θB

variable {i j : ℕ} {θA θB ρ lam : ℝ}

theorem slack_row_nonneg (t : Fin (min i j + 1)) :
    0 ≤ slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) := by
  have ht : (t : ℕ) ≤ min i j := by have := t.isLt; omega
  have h1 : ((t : ℕ) : ℤ) ≤ (i : ℤ) := by
    exact_mod_cast le_trans ht (min_le_left i j)
  have h2 : ((t : ℕ) : ℤ) ≤ (j : ℤ) := by
    exact_mod_cast le_trans ht (min_le_right i j)
  have := slack_nonneg (i := (i : ℤ)) (j := (j : ℤ)) (t := ((t : ℕ) : ℤ))
    (Int.natCast_nonneg _) h1 h2
  have hcast : (0 : ℝ) ≤ ((slack (i : ℤ) (j : ℤ) ((t : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast this
  rwa [slack_intCast] at hcast

theorem slack_row_ge_min (t : Fin (min i j + 1)) :
    bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)
      ≤ slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) := by
  have ht : ((t : ℕ) : ℤ) ≤ ((min i j : ℕ) : ℤ) := by
    have := t.isLt
    exact_mod_cast (by omega : (t : ℕ) ≤ min i j)
  have hz := slack_min_le (i := (i : ℤ)) (j := (j : ℤ)) (t := ((t : ℕ) : ℤ))
    (m := ((min i j : ℕ) : ℤ)) (Int.natCast_nonneg _) ht
  rw [slack_min_eq] at hz
  have hcast : ((bigS (i : ℤ) (j : ℤ) - ((min i j : ℕ) : ℤ) * (((min i j : ℕ) : ℤ) - 1) : ℤ) : ℝ)
      ≤ ((slack (i : ℤ) (j : ℤ) ((t : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hz
  rw [slack_intCast] at hcast
  push_cast [bigS] at hcast ⊢
  linarith

theorem exists_row_le_of_mulVec (hρ : 0 ≤ ρ) {μ : ℝ} {v : Fin (min i j + 1) → ℝ}
    (hv : v ≠ 0) (heig : (T i j θA θB ρ) *ᵥ v = μ • v) :
    ∃ t : Fin (min i j + 1),
      floorMu i j θA θB + slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) ≤ μ := by
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (T i j θA θB ρ)) μ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [Matrix.toLin'_apply] using heig
  obtain ⟨t, ht⟩ := eigenvalue_mem_ball hev
  refine ⟨t, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq] at ht
  have habs : ∀ s : Fin (min i j + 1), ‖T i j θA θB ρ t s‖ = |T i j θA θB ρ t s| := fun _ =>
    Real.norm_eq_abs _
  simp only [habs] at ht
  have hkey := T_diag_sub_radius (i := i) (j := j) (θA := θA) (θB := θB) hρ t
  have h1 : T i j θA θB ρ t t - ∑ s ∈ Finset.univ.erase t, |T i j θA θB ρ t s| ≤ μ := by
    have := abs_le.1 ht
    linarith [this.1]
  unfold floorMu
  linarith [hkey ▸ h1]

theorem T_eigen_ge_sharp (hρ : 0 ≤ ρ) {μ : ℝ} {v : Fin (min i j + 1) → ℝ}
    (hv : v ≠ 0) (heig : (T i j θA θB ρ) *ᵥ v = μ • v) :
    floorMu i j θA θB
        + (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) ≤ μ := by
  obtain ⟨t, ht⟩ := exists_row_le_of_mulVec hρ hv heig
  linarith [slack_row_ge_min (i := i) (j := j) t]

theorem T_eigen_ge_floor (hρ : 0 ≤ ρ) {μ : ℝ} {v : Fin (min i j + 1) → ℝ}
    (hv : v ≠ 0) (heig : (T i j θA θB ρ) *ᵥ v = μ • v) :
    floorMu i j θA θB ≤ μ := by
  obtain ⟨t, ht⟩ := exists_row_le_of_mulVec hρ hv heig
  linarith [slack_row_nonneg (i := i) (j := j) t]

theorem Te_mulVec_iff (hlam : lam ≠ 0) {μ : ℝ} {v : Fin (min i j + 1) → ℝ} :
    (Te i j lam θA θB ρ) *ᵥ v = μ • v ↔
      (T i j (lam * θA) (lam * θB) (lam * ρ)) *ᵥ v = (lam * μ) • v := by
  unfold Te
  rw [Matrix.smul_mulVec]
  constructor
  · intro h
    have := congrArg (fun w => lam • w) h
    simpa [smul_smul, mul_inv_cancel₀ hlam] using this
  · intro h
    rw [h]
    rw [smul_smul, inv_mul_cancel_left₀ hlam]

theorem Te_eigen_ge_sharp (hlam : 0 < lam) (hρ : 0 ≤ ρ) {μ : ℝ} {v : Fin (min i j + 1) → ℝ}
    (hv : v ≠ 0) (heig : (Te i j lam θA θB ρ) *ᵥ v = μ • v) :
    floorMu i j θA θB
        + (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam
      ≤ μ := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have h := T_eigen_ge_sharp (i := i) (j := j) (θA := lam * θA) (θB := lam * θB)
    (ρ := lam * ρ) (mul_nonneg hlam.le hρ) hv ((Te_mulVec_iff hlam').1 heig)
  unfold floorMu at h ⊢
  have key : (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam
      ≤ μ - ((i : ℝ) * θA + (j : ℝ) * θB) := by
    rw [div_le_iff₀ hlam]
    nlinarith [h]
  linarith

theorem Te_eigen_ge_floor (hlam : 0 < lam) (hρ : 0 ≤ ρ) {μ : ℝ} {v : Fin (min i j + 1) → ℝ}
    (hv : v ≠ 0) (heig : (Te i j lam θA θB ρ) *ᵥ v = μ • v) :
    floorMu i j θA θB ≤ μ := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have h := T_eigen_ge_floor (i := i) (j := j) (θA := lam * θA) (θB := lam * θB)
    (ρ := lam * ρ) (mul_nonneg hlam.le hρ) hv ((Te_mulVec_iff hlam').1 heig)
  unfold floorMu at h ⊢
  have h2 : lam * ((i : ℝ) * θA + (j : ℝ) * θB) ≤ lam * μ := by nlinarith [h]
  exact le_of_mul_le_mul_left h2 hlam

end Rhone.LinearAlgebra.Spectral
