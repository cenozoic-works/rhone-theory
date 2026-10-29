/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Floor
public import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! # The spectral floor for operators on matching space with the same row radii -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset

theorem exists_row_le_of_mulVec' {Mt : Type*} [Fintype Mt] [DecidableEq Mt]
    (A : Matrix Mt Mt ℝ) {μ : ℝ} {v : Mt → ℝ} (hv : v ≠ 0) (heig : A *ᵥ v = μ • v) :
    ∃ m : Mt, A m m - ∑ m' ∈ Finset.univ.erase m, |A m m'| ≤ μ := by
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [Matrix.toLin'_apply] using heig
  obtain ⟨m, hm⟩ := eigenvalue_mem_ball hev
  refine ⟨m, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq] at hm
  have habs : ∀ m' : Mt, ‖A m m'‖ = |A m m'| := fun _ => Real.norm_eq_abs _
  simp only [habs] at hm
  have := abs_le.1 hm
  linarith [this.1]

theorem slack_nat_nonneg (i j t : ℕ) (h : t ≤ min i j) :
    0 ≤ slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) := by
  have h1 : ((t : ℕ) : ℤ) ≤ (i : ℤ) := by exact_mod_cast le_trans h (min_le_left i j)
  have h2 : ((t : ℕ) : ℤ) ≤ (j : ℤ) := by exact_mod_cast le_trans h (min_le_right i j)
  have hz := slack_nonneg (i := (i : ℤ)) (j := (j : ℤ)) (t := ((t : ℕ) : ℤ))
    (Int.natCast_nonneg _) h1 h2
  have hcast : (0 : ℝ) ≤ ((slack (i : ℤ) (j : ℤ) ((t : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hz
  rwa [slack_intCast] at hcast

theorem slack_nat_ge_min (i j t : ℕ) (h : t ≤ min i j) :
    bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)
      ≤ slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) := by
  have ht : ((t : ℕ) : ℤ) ≤ ((min i j : ℕ) : ℤ) := by exact_mod_cast h
  have hz := slack_min_le (i := (i : ℤ)) (j := (j : ℤ)) (t := ((t : ℕ) : ℤ))
    (m := ((min i j : ℕ) : ℤ)) (Int.natCast_nonneg _) ht
  rw [slack_min_eq] at hz
  have hcast : ((bigS (i : ℤ) (j : ℤ) - ((min i j : ℕ) : ℤ) * (((min i j : ℕ) : ℤ) - 1) : ℤ) : ℝ)
      ≤ ((slack (i : ℤ) (j : ℤ) ((t : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hz
  rw [slack_intCast] at hcast
  push_cast [bigS] at hcast ⊢
  linarith

variable {Mt : Type*} [Fintype Mt] [DecidableEq Mt]

theorem matching_eigen_ge_sharp (A : Matrix Mt Mt ℝ) (i j : ℕ) (θA θB ρ : ℝ) (sz : Mt → ℕ)
    (hsz : ∀ m, sz m ≤ min i j)
    (hdiag : ∀ m, A m m = Tdiag i j θA θB ρ (sz m))
    (hrad : ∀ m, ∑ m' ∈ Finset.univ.erase m, |A m m'|
      = ρ * ((sz m : ℕ) : ℝ) + 2 * ((i : ℝ) - ((sz m : ℕ) : ℝ)) * ((j : ℝ) - ((sz m : ℕ) : ℝ)))
    {μ : ℝ} {v : Mt → ℝ} (hv : v ≠ 0) (heig : A *ᵥ v = μ • v) :
    floorMu i j θA θB
        + (bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) ≤ μ := by
  obtain ⟨m, hm⟩ := exists_row_le_of_mulVec' A hv heig
  rw [hdiag m, hrad m] at hm
  have hkey : Tdiag i j θA θB ρ (sz m)
      - (ρ * ((sz m : ℕ) : ℝ) + 2 * ((i : ℝ) - ((sz m : ℕ) : ℝ)) * ((j : ℝ) - ((sz m : ℕ) : ℝ)))
      = floorMu i j θA θB + slack (i : ℝ) (j : ℝ) ((sz m : ℕ) : ℝ) := by
    unfold Tdiag floorMu slack
    ring
  rw [hkey] at hm
  linarith [slack_nat_ge_min i j (sz m) (hsz m)]

theorem matching_eigen_ge_floor (A : Matrix Mt Mt ℝ) (i j : ℕ) (θA θB ρ : ℝ) (sz : Mt → ℕ)
    (hsz : ∀ m, sz m ≤ min i j)
    (hdiag : ∀ m, A m m = Tdiag i j θA θB ρ (sz m))
    (hrad : ∀ m, ∑ m' ∈ Finset.univ.erase m, |A m m'|
      = ρ * ((sz m : ℕ) : ℝ) + 2 * ((i : ℝ) - ((sz m : ℕ) : ℝ)) * ((j : ℝ) - ((sz m : ℕ) : ℝ)))
    {μ : ℝ} {v : Mt → ℝ} (hv : v ≠ 0) (heig : A *ᵥ v = μ • v) :
    floorMu i j θA θB ≤ μ := by
  obtain ⟨m, hm⟩ := exists_row_le_of_mulVec' A hv heig
  rw [hdiag m, hrad m] at hm
  have hkey : Tdiag i j θA θB ρ (sz m)
      - (ρ * ((sz m : ℕ) : ℝ) + 2 * ((i : ℝ) - ((sz m : ℕ) : ℝ)) * ((j : ℝ) - ((sz m : ℕ) : ℝ)))
      = floorMu i j θA θB + slack (i : ℝ) (j : ℝ) ((sz m : ℕ) : ℝ) := by
    unfold Tdiag floorMu slack
    ring
  rw [hkey] at hm
  linarith [slack_nat_nonneg i j (sz m) (hsz m)]

theorem matching_epoch_eigen_ge_floor (A : Matrix Mt Mt ℝ) (i j : ℕ) (θA θB ρ lam : ℝ)
    (hlam : 0 < lam) (sz : Mt → ℕ) (hsz : ∀ m, sz m ≤ min i j)
    (hdiag : ∀ m, A m m = Tdiag i j (lam * θA) (lam * θB) (lam * ρ) (sz m))
    (hrad : ∀ m, ∑ m' ∈ Finset.univ.erase m, |A m m'|
      = (lam * ρ) * ((sz m : ℕ) : ℝ)
        + 2 * ((i : ℝ) - ((sz m : ℕ) : ℝ)) * ((j : ℝ) - ((sz m : ℕ) : ℝ)))
    {μ : ℝ} {v : Mt → ℝ} (hv : v ≠ 0) (heig : (lam⁻¹ • A) *ᵥ v = μ • v) :
    floorMu i j θA θB ≤ μ := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have heig' : A *ᵥ v = (lam * μ) • v := by
    have := congrArg (fun w => lam • w) heig
    simpa [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hlam'] using this
  have h := matching_eigen_ge_floor A i j (lam * θA) (lam * θB) (lam * ρ) sz hsz hdiag hrad
    hv heig'
  unfold floorMu at h ⊢
  have h2 : lam * ((i : ℝ) * θA + (j : ℝ) * θB) ≤ lam * μ := by nlinarith [h]
  exact le_of_mul_le_mul_left h2 hlam

end Rhone.LinearAlgebra.Spectral
