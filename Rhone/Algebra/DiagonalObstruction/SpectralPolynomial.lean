/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Rhone.Algebra.DiagonalObstruction.CollisionLabels
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # The monic characteristic polynomial of the spectral matrix over `ℤ[ρ]` -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

open Polynomial LinearAlgebra.Tridiag

def spectralMatrix (R : Type*) [CommRing R] (m : ℕ) (ρ : R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  trid (fun t => (coalDiag m t : R) + ρ * t)
    (fun t => -2 * ((m : R) - t) ^ 2)
    (fun t => -(ρ * ((t : R) + 1))) (m + 1)

noncomputable def spectralPolynomial (m : ℕ) : Polynomial (Polynomial ℤ) :=
  (spectralMatrix ℤ[X] m X).charpoly

theorem spectralPolynomial_monic (m : ℕ) : (spectralPolynomial m).Monic :=
  Matrix.charpoly_monic _

theorem spectralPolynomial_natDegree (m : ℕ) :
    (spectralPolynomial m).natDegree = m + 1 := by
  simp [spectralPolynomial]

theorem charmatrix_trid {R : Type*} [CommRing R] (d b c : ℕ → R) (n : ℕ) :
    (trid d b c n).charmatrix =
      trid (fun t => X - C (d t)) (fun t => -C (b t)) (fun t => -C (c t)) n := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.charmatrix_apply_eq, tridEntry]
  · rw [Matrix.charmatrix_apply_ne _ _ _ hij]
    have hval : (j : ℕ) ≠ (i : ℕ) := by
      intro h
      exact hij (Fin.ext h.symm)
    simp only [trid_apply, tridEntry, ite_eq_right hval]
    split_ifs <;> simp

theorem charpoly_trid {R : Type*} [CommRing R] (d b c : ℕ → R) (n : ℕ) :
    (trid d b c n).charpoly =
      cont (fun t => X - C (d t)) (fun t => -C (b t)) (fun t => -C (c t)) n := by
  rw [Matrix.charpoly, charmatrix_trid, det_trid_eq_cont]

theorem spectralPolynomial_eq_cont (m : ℕ) :
    spectralPolynomial m =
      cont (R := Polynomial (Polynomial ℤ))
        (fun t => X - C (C (coalDiag m t) + X * C (t : ℤ)))
        (fun t => C (C (2 * ((m : ℤ) - t) ^ 2)))
        (fun t => C (X * C ((t : ℤ) + 1))) (m + 1) := by
  rw [spectralPolynomial, spectralMatrix, charpoly_trid]
  congr 1 <;> funext t <;> simp [map_ofNat]

theorem spectralMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : ℕ) (ρ : R) :
    (spectralMatrix R m ρ).map f = spectralMatrix S m (f ρ) := by
  ext i j
  simp only [spectralMatrix, Matrix.map_apply, trid_apply, tridEntry, apply_ite f]
  split_ifs <;> simp [map_ofNat]

theorem spectralMatrix_zero_upper (R : Type*) [CommRing R] (m : ℕ) :
    (spectralMatrix R m 0).IsUpperTriangular := by
  intro i j hij
  have hval : (j : ℕ) < (i : ℕ) := hij
  simp only [spectralMatrix, trid_apply, tridEntry,
    ite_eq_right (by omega : (j : ℕ) ≠ (i : ℕ)),
    ite_eq_right (by omega : (j : ℕ) ≠ (i : ℕ) + 1)]
  split_ifs <;> simp

theorem spectralPolynomial_zero_fiber (m : ℕ) :
    (spectralPolynomial m).map (evalRingHom (0 : ℤ)) =
      ∏ t : Fin (m + 1), (X - C (coalDiag m t)) := by
  rw [spectralPolynomial, ← Matrix.charpoly_map, spectralMatrix_map]
  simp only [coe_evalRingHom, eval_X]
  rw [Matrix.charpoly_of_isUpperTriangular _ (spectralMatrix_zero_upper ℤ m)]
  apply Finset.prod_congr rfl
  intro t _
  simp [spectralMatrix, tridEntry]

end Rhone.Algebra.DiagonalObstruction
