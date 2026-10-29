/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Tactic.Ring

/-! # Diagonal blocks depend only on the sum of mutation parameters -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial LinearAlgebra.Tridiag

variable {R : Type*} [CommRing R]

theorem dcoef_diagonal_parameter_sum (m t : ℕ) (θA θB ρ : R) :
    dcoef R m m θA θB ρ t = dcoef R m m (θA + θB) 0 ρ t := by
  simp only [dcoef]
  ring

theorem T_diagonal_parameter_sum (m : ℕ) (θA θB ρ : R) :
    T R m m θA θB ρ = T R m m (θA + θB) 0 ρ := by
  unfold T
  congr 1
  funext t
  exact dcoef_diagonal_parameter_sum m t θA θB ρ

theorem E_diagonal_parameter_sum (m : ℕ) (θA θB ρ : R) :
    E R m m θA θB ρ = E R m m (θA + θB) 0 ρ := by
  unfold E
  rw [T_diagonal_parameter_sum]

theorem E_diagonal_eq_of_sum_eq (m : ℕ) {θA θB θA' θB' : R}
    (h : θA + θB = θA' + θB') (ρ : R) :
    E R m m θA θB ρ = E R m m θA' θB' ρ := by
  rw [E_diagonal_parameter_sum, h, ← E_diagonal_parameter_sum]

theorem E_diagonal_polynomial_parameter_sum (m : ℕ) (θA θB : R) :
    E R[X] m m (Polynomial.C θA) (Polynomial.C θB) Polynomial.X =
      E R[X] m m (Polynomial.C (θA + θB)) 0 Polynomial.X := by
  rw [E_diagonal_parameter_sum, ← Polynomial.C_add]

noncomputable def diagonalFamily (R : Type*) [CommRing R] (m : ℕ) : R[X][X] :=
  E R[X][X] m m (Polynomial.C Polynomial.X) 0 Polynomial.X

theorem diagonalFamily_specialization (m : ℕ) (θA θB : R) :
    (diagonalFamily R m).map (Polynomial.evalRingHom (θA + θB)) =
      E R[X] m m (Polynomial.C θA) (Polynomial.C θB) Polynomial.X := by
  unfold diagonalFamily
  rw [← Polynomial.coe_mapRingHom,
    LinearAlgebra.Tridiag.E_map (Polynomial.mapRingHom (Polynomial.evalRingHom (θA + θB)))]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom,
    Polynomial.eval_X, Polynomial.map_zero, Polynomial.map_X]
  rw [E_diagonal_polynomial_parameter_sum]

end Rhone.Algebra.GaloisSpecialization
