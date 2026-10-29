/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Contraction

/-! # Multi-epoch product bound in the `W`-metrics, with the seam factor -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset

variable {i j : ℕ}

theorem W_ratio_pow {r r' : ℝ} (hr : r ≠ 0) (i j : ℕ) (t : ℕ) :
    W i j r' t = (r' / r) ^ t * W i j r t := by
  have hrt : r ^ t ≠ 0 := pow_ne_zero t hr
  have hi : (Nat.factorial i : ℝ) ≠ 0 := factorial_cast_ne_zero i
  have hj : (Nat.factorial j : ℝ) ≠ 0 := factorial_cast_ne_zero j
  have h2 : (2 : ℝ) ^ t ≠ 0 := by positivity
  unfold W
  rw [div_pow]
  field_simp

theorem pow_le_max_one_pow {q : ℝ} (hq : 0 < q) {t m : ℕ} (htm : t ≤ m) :
    q ^ t ≤ max 1 (q ^ m) := by
  rcases le_total q 1 with h | h
  · exact le_trans (pow_le_one₀ hq.le h) (le_max_left _ _)
  · exact le_trans (pow_le_pow_right₀ h htm) (le_max_right _ _)

theorem innerW_seam_le {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (u : Fin (min i j + 1) → ℝ) :
    innerW i j r' u u ≤ max 1 ((r / r') ^ (min i j)) * innerW i j r u u := by
  unfold innerW
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hWr : 0 < W i j r (t : ℕ) := W_pos hr _
  have hWr' : W i j r' (t : ℕ) = (r' / r) ^ (t : ℕ) * W i j r (t : ℕ) :=
    W_ratio_pow (ne_of_gt hr) i j (t : ℕ)
  have hq : 0 < r / r' := div_pos hr hr'
  have hq' : (0 : ℝ) < r' / r := div_pos hr' hr
  have htm : (t : ℕ) ≤ min i j := by have := t.isLt; omega
  have hqt : (r / r') ^ (t : ℕ) ≤ max 1 ((r / r') ^ (min i j)) := pow_le_max_one_pow hq htm
  have hne : ((r' / r) ^ (t : ℕ)) ≠ 0 := ne_of_gt (pow_pos hq' _)
  have hinv : ((r' / r) ^ (t : ℕ))⁻¹ = (r / r') ^ (t : ℕ) := by
    rw [← inv_pow, inv_div]
  have key : u t * u t / W i j r' (t : ℕ)
      = (r / r') ^ (t : ℕ) * (u t * u t / W i j r (t : ℕ)) := by
    rw [hWr', ← hinv]
    field_simp
  rw [key]
  exact mul_le_mul_of_nonneg_right hqt
    (div_nonneg (mul_self_nonneg _) hWr.le)

theorem seam_self_eq_one (i j : ℕ) {r : ℝ} (hr : r ≠ 0) :
    max 1 ((r / r) ^ (min i j)) = 1 := by
  rw [div_self hr, one_pow, max_self]

variable {θA1 θB1 ρ1 lam1 θA2 θB2 ρ2 lam2 : ℝ}

theorem innerW_two_epoch (hlam1 : 0 < lam1) (hρ1 : 0 < ρ1) (hlam2 : 0 < lam2) (hρ2 : 0 < ρ2)
    {s1 s2 : ℝ} (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (x : Fin (min i j + 1) → ℝ) :
    innerW i j (lam2 * ρ2)
        (NormedSpace.exp (s2 • (-Te i j lam2 θA2 θB2 ρ2)) *ᵥ
          (NormedSpace.exp (s1 • (-Te i j lam1 θA1 θB1 ρ1)) *ᵥ x))
        (NormedSpace.exp (s2 • (-Te i j lam2 θA2 θB2 ρ2)) *ᵥ
          (NormedSpace.exp (s1 • (-Te i j lam1 θA1 θB1 ρ1)) *ᵥ x))
      ≤ Real.exp (-(s2 * floorMu i j θA2 θB2)) ^ 2
          * (max 1 (((lam1 * ρ1) / (lam2 * ρ2)) ^ (min i j))
            * (Real.exp (-(s1 * floorMu i j θA1 θB1)) ^ 2 * innerW i j (lam1 * ρ1) x x)) := by
  set y := NormedSpace.exp (s1 • (-Te i j lam1 θA1 θB1 ρ1)) *ᵥ x with hy
  have hr1 : 0 < lam1 * ρ1 := mul_pos hlam1 hρ1
  have hr2 : 0 < lam2 * ρ2 := mul_pos hlam2 hρ2
  have hE2 : (0 : ℝ) ≤ Real.exp (-(s2 * floorMu i j θA2 θB2)) ^ 2 := sq_nonneg _
  have hκ : (0 : ℝ) ≤ max 1 (((lam1 * ρ1) / (lam2 * ρ2)) ^ (min i j)) :=
    le_trans zero_le_one (le_max_left _ _)
  have step1 := innerW_exp_neg_smul_Te_le_floor (i := i) (j := j) (θA := θA2) (θB := θB2)
    hlam2 hρ2 hs2 y
  have step2 := innerW_seam_le (i := i) (j := j) hr1 hr2 y
  have step3 := innerW_exp_neg_smul_Te_le_floor (i := i) (j := j) (θA := θA1) (θB := θB1)
    hlam1 hρ1 hs1 x
  refine le_trans step1 ?_
  refine mul_le_mul_of_nonneg_left ?_ hE2
  refine le_trans step2 ?_
  exact mul_le_mul_of_nonneg_left step3 hκ

def applyChain {n : ℕ} (F : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, x => x
  | (e + 1), x => F e *ᵥ applyChain F e x

theorem innerW_chain (r : ℕ → ℝ) (F : ℕ → Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) ℝ)
    (c : ℕ → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hstep : ∀ e u, innerW i j (r (e + 1)) (F e *ᵥ u) (F e *ᵥ u) ≤ c e * innerW i j (r e) u u)
    (E : ℕ) (x : Fin (min i j + 1) → ℝ) :
    innerW i j (r E) (applyChain F E x) (applyChain F E x)
      ≤ (∏ e ∈ Finset.range E, c e) * innerW i j (r 0) x x := by
  induction E with
  | zero => simp [applyChain]
  | succ E ih =>
    have h1 := hstep E (applyChain F E x)
    have h2 := mul_le_mul_of_nonneg_left ih (hc E)
    rw [Finset.prod_range_succ]
    calc innerW i j (r (E + 1)) (applyChain F (E + 1) x) (applyChain F (E + 1) x)
        ≤ c E * innerW i j (r E) (applyChain F E x) (applyChain F E x) := h1
      _ ≤ c E * ((∏ e ∈ Finset.range E, c e) * innerW i j (r 0) x x) := h2
      _ = (∏ e ∈ Finset.range E, c e) * c E * innerW i j (r 0) x x := by ring

variable {θAf θBf ρf lamf sf : ℕ → ℝ}

theorem innerW_multi_epoch (hlam : ∀ e, 0 < lamf e) (hρ : ∀ e, 0 < ρf e)
    (hs : ∀ e, 0 ≤ sf e) (E : ℕ) (x : Fin (min i j + 1) → ℝ) :
    innerW i j (lamf E * ρf E)
        (applyChain (fun e =>
          NormedSpace.exp (sf e • (-Te i j (lamf e) (θAf e) (θBf e) (ρf e)))) E x)
        (applyChain (fun e =>
          NormedSpace.exp (sf e • (-Te i j (lamf e) (θAf e) (θBf e) (ρf e)))) E x)
      ≤ (∏ e ∈ Finset.range E,
            max 1 ((lamf e * ρf e / (lamf (e + 1) * ρf (e + 1))) ^ (min i j))
              * Real.exp (-(sf e * floorMu i j (θAf e) (θBf e))) ^ 2)
        * innerW i j (lamf 0 * ρf 0) x x := by
  refine innerW_chain (fun e => lamf e * ρf e) _ _ (fun e => ?_) (fun e u => ?_) E x
  · exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (sq_nonneg _)
  · have hre : 0 < lamf e * ρf e := mul_pos (hlam e) (hρ e)
    have hre' : 0 < lamf (e + 1) * ρf (e + 1) := mul_pos (hlam (e + 1)) (hρ (e + 1))
    have hκ : (0 : ℝ) ≤ max 1 ((lamf e * ρf e / (lamf (e + 1) * ρf (e + 1))) ^ (min i j)) :=
      le_trans zero_le_one (le_max_left _ _)
    refine le_trans (innerW_seam_le (i := i) (j := j) hre hre' _) ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (innerW_exp_neg_smul_Te_le_floor (i := i) (j := j) (θA := θAf e) (θB := θBf e)
        (hlam e) (hρ e) (hs e) u) hκ

end Rhone.LinearAlgebra.Spectral
