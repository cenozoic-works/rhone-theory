/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Floor

/-! # Algebraic core of the sup-norm decay bound for the epoch generator -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Finset
open scoped Matrix

variable {i j : ℕ} {θA θB ρ lam hstep : ℝ}

theorem Te_offdiag_abs_sum (hlam : 0 < lam) (t : Fin (min i j + 1)) :
    ∑ s ∈ Finset.univ.erase t, |Te i j lam θA θB ρ t s|
      = lam⁻¹ * ∑ s ∈ Finset.univ.erase t, |T i j (lam * θA) (lam * θB) (lam * ρ) t s| := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold Te
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hlam)]

theorem Te_diag_sub_radius (hlam : 0 < lam) (hρ : 0 ≤ ρ) (t : Fin (min i j + 1)) :
    Te i j lam θA θB ρ t t - ∑ s ∈ Finset.univ.erase t, |Te i j lam θA θB ρ t s|
      = floorMu i j θA θB + slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) / lam := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hkey := T_diag_sub_radius (i := i) (j := j) (θA := lam * θA) (θB := lam * θB)
    (ρ := lam * ρ) (mul_nonneg hlam.le hρ) t
  rw [Te_offdiag_abs_sum hlam]
  have hdiag : Te i j lam θA θB ρ t t = lam⁻¹ * T i j (lam * θA) (lam * θB) (lam * ρ) t t := by
    unfold Te
    rw [Matrix.smul_apply, smul_eq_mul]
  rw [hdiag, ← mul_sub, hkey]
  unfold floorMu
  field_simp

theorem Te_offdiag_nonpos (hlam : 0 < lam) (hρ : 0 ≤ ρ) {t s : Fin (min i j + 1)}
    (hts : s ≠ t) : Te i j lam θA θB ρ t s ≤ 0 := by
  have hle : (t : ℕ) ≤ min i j := by have := t.isLt; omega
  have hti : ((t : ℕ) : ℝ) ≤ (i : ℝ) := by
    have h : (t : ℕ) ≤ i := le_trans hle (min_le_left i j)
    exact_mod_cast h
  have htj : ((t : ℕ) : ℝ) ≤ (j : ℝ) := by
    have h : (t : ℕ) ≤ j := le_trans hle (min_le_right i j)
    exact_mod_cast h
  have hne : (s : ℕ) ≠ (t : ℕ) := fun hc => hts (Fin.ext hc)
  by_cases h2 : (s : ℕ) = (t : ℕ) + 1
  · rw [Te_apply_sup (ne_of_gt hlam) h2, div_nonpos_iff]
    right
    exact ⟨by nlinarith, hlam.le⟩
  · by_cases h3 : (t : ℕ) = (s : ℕ) + 1
    · rw [Te_apply_sub (ne_of_gt hlam) h3]
      have hnn : 0 ≤ ρ * ((t : ℕ) : ℝ) := mul_nonneg hρ (Nat.cast_nonneg _)
      linarith
    · unfold Te
      rw [Matrix.smul_apply, smul_eq_mul, T_apply_zero hne h2 h3, mul_zero]

theorem neg_Te_row_measure_le (hlam : 0 < lam) (hρ : 0 ≤ ρ) (t : Fin (min i j + 1)) :
    (-Te i j lam θA θB ρ) t t + ∑ s ∈ Finset.univ.erase t, |(-Te i j lam θA θB ρ) t s|
      ≤ -(floorMu i j θA θB
          + (bigS (i : ℝ) (j : ℝ)
            - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam) := by
  simp only [Matrix.neg_apply, abs_neg]
  have hkey := Te_diag_sub_radius (i := i) (j := j) (θA := θA) (θB := θB) hlam hρ t
  have hslack := slack_row_ge_min (i := i) (j := j) t
  have hdiv : (bigS (i : ℝ) (j : ℝ)
      - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam
      ≤ slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) / lam :=
    div_le_div_of_nonneg_right hslack hlam.le
  linarith

theorem shifted_row_sum_nonpos (hlam : 0 < lam) (hρ : 0 ≤ ρ) (t : Fin (min i j + 1)) :
    ((-Te i j lam θA θB ρ) t t
        + (floorMu i j θA θB
          + (bigS (i : ℝ) (j : ℝ)
            - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam))
      + ∑ s ∈ Finset.univ.erase t, |(-Te i j lam θA θB ρ) t s| ≤ 0 := by
  have h := neg_Te_row_measure_le (i := i) (j := j) (θA := θA) (θB := θB) hlam hρ t
  linarith

theorem one_sub_smul_abs_row_sum_le (hlam : 0 < lam) (hρ : 0 ≤ ρ) (hh : 0 ≤ hstep)
    (t : Fin (min i j + 1)) (hdiag : hstep * Te i j lam θA θB ρ t t ≤ 1) :
    ∑ s, |(1 - hstep • Te i j lam θA θB ρ) t s|
      ≤ 1 - hstep * (floorMu i j θA θB
          + (bigS (i : ℝ) (j : ℝ)
            - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam) := by
  have hdiagEntry : (1 - hstep • Te i j lam θA θB ρ) t t
      = 1 - hstep * Te i j lam θA θB ρ t t := by
    simp [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply]
  have hoff : ∀ s ∈ Finset.univ.erase t,
      |(1 - hstep • Te i j lam θA θB ρ) t s| = hstep * |Te i j lam θA θB ρ t s| := by
    intro s hs
    have hne : t ≠ s := by
      have hst := (Finset.mem_erase.1 hs).1
      exact fun hc => hst hc.symm
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, Matrix.smul_apply, smul_eq_mul, zero_sub,
      abs_neg, abs_mul, abs_of_nonneg hh]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t), hdiagEntry,
    Finset.sum_congr rfl hoff, ← Finset.mul_sum, abs_of_nonneg (by linarith)]
  have hkey := Te_diag_sub_radius (i := i) (j := j) (θA := θA) (θB := θB) hlam hρ t
  have hslack := slack_row_ge_min (i := i) (j := j) t
  have hdiv : (bigS (i : ℝ) (j : ℝ)
      - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam
      ≤ slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) / lam :=
    div_le_div_of_nonneg_right hslack hlam.le
  nlinarith [hkey, hdiv, hh]

end Rhone.LinearAlgebra.Spectral
