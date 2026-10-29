/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalObstruction.SpectralPolynomial
public import Rhone.Algebra.DiagonalObstruction.SimpleFiber
public import Rhone.Analysis.Rescale.Rescale

/-! # The spectral characteristic polynomial evaluated as the diagonal determinant `E_{m,m}` -/

@[expose] public section

namespace Rhone.Analysis.DiagonalObstruction
open Polynomial Matrix LinearAlgebra.Tridiag
variable {R : Type*} [CommRing R]

private theorem dcoef_eq_coalDiag {m t : ℕ} (hm : 1 ≤ m) (ht : t ≤ m) (θ ρ : R) :
    dcoef R m m θ 0 ρ t = (Algebra.DiagonalObstruction.coalDiag m t : R) + θ * m + ρ * t := by
  have hsub : t ≤ m + m := by omega
  have hsub1 : 1 ≤ m + m - t := by omega
  simp only [dcoef, zero_mul, add_zero, Algebra.DiagonalObstruction.coalDiag_cast]
  push_cast [Nat.cast_sub hsub, Nat.cast_sub hsub1]
  ring

private theorem bcoef_eq_square {m t : ℕ} (ht : t ≤ m) :
    bcoef R m m t = -2 * ((m : R) - t) ^ 2 := by
  simp only [bcoef, Nat.cast_mul, Nat.cast_sub ht]
  ring

theorem spectral_shift_eq_neg_trid {m : ℕ} (hm : 1 ≤ m) (θ ρ : R) :
    Matrix.scalar (Fin (m + 1)) (-θ * m) - Algebra.DiagonalObstruction.spectralMatrix R m ρ =
      -trid (dcoef R m m θ 0 ρ) (bcoef R m m) (ccoef R ρ) (m + 1) := by
  ext i j
  have hi : (i : ℕ) ≤ m := by omega
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar_apply, Algebra.DiagonalObstruction.spectralMatrix, tridEntry,
        dcoef_eq_coalDiag hm hi]
    ring
  · have hval : (j : ℕ) ≠ (i : ℕ) := by
      intro h
      exact hij (Fin.ext h.symm)
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hij, Algebra.DiagonalObstruction.spectralMatrix, trid_apply,
          tridEntry, ite_eq_right hval]
    split_ifs <;> simp [bcoef_eq_square hi, ccoef]

theorem spectral_charpoly_eval_eq_E {m : ℕ} (hm : 1 ≤ m) (θ ρ : R) :
    (Algebra.DiagonalObstruction.spectralMatrix R m ρ).charpoly.eval (-θ * m) =
      (-1) ^ (m + 1) * E R m m θ 0 ρ := by
  rw [E, T, Nat.min_self]
  rw [Matrix.eval_charpoly, spectral_shift_eq_neg_trid hm, Matrix.det_neg, Fintype.card_fin]

theorem spectralPolynomial_map (f : Polynomial ℤ →+* R) (m : ℕ) :
    (Algebra.DiagonalObstruction.spectralPolynomial m).map f =
        (Algebra.DiagonalObstruction.spectralMatrix R m (f X)).charpoly := by
  rw [Algebra.DiagonalObstruction.spectralPolynomial, ← Matrix.charpoly_map,
      Algebra.DiagonalObstruction.spectralMatrix_map]

theorem spectralPolynomial_eval₂_eq_E {m : ℕ} (hm : 1 ≤ m)
    (f : Polynomial ℤ →+* R) (θ : R) :
    (Algebra.DiagonalObstruction.spectralPolynomial m).eval₂ f (-θ * m) =
      (-1) ^ (m + 1) * E R m m θ 0 (f X) := by
  rw [← eval_map, spectralPolynomial_map, spectral_charpoly_eval_eq_E hm]

theorem spectral_charpoly_eval_eq_cont (m : ℕ) (z ρ : R) :
    (Algebra.DiagonalObstruction.spectralMatrix R m ρ).charpoly.eval z =
      cont (fun t => z - (Algebra.DiagonalObstruction.coalDiag m t : R) - ρ * t)
        (fun t => 2 * ((m : R) - t) ^ 2)
        (fun t => ρ * ((t : R) + 1)) (m + 1) := by
  rw [Algebra.DiagonalObstruction.spectralMatrix, Algebra.DiagonalObstruction.charpoly_trid, ←
      Polynomial.coe_evalRingHom,
    Rescale.cont_map]
  congr 1 <;> funext t <;> simp only [coe_evalRingHom, eval_sub, eval_X,
    eval_C, eval_neg] <;> ring

theorem markedPoint_spectral_coordinate (m : ℕ) :
    -Algebra.DiagonalObstruction.markedPoint m * (m : ℚ) =
        (Algebra.DiagonalObstruction.coalDiag m 0 : ℚ) := by
  simp only [Algebra.DiagonalObstruction.markedPoint, Algebra.DiagonalObstruction.coalDiag_cast,
      Nat.cast_zero, sub_zero]
  ring

end Rhone.Analysis.DiagonalObstruction
