/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Rhone.Algebra.DiagonalIrreducibility.Quartic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # E₃₃ is irreducible in the mutation sum over ℚ(ρ), with degree four -/

@[expose] public section

namespace Rhone.Algebra.DiagonalIrreducibility
open Polynomial

noncomputable def E33Theta : Polynomial (Polynomial ℚ) :=
  C 81 * X^4 + C (162*X + 1836) * X^3 +
  C (99*X^2 + 2754*X + 14148) * X^2 +
  C (18*X^3 + 1062*X^2 + 14436*X + 43200) * X +
  C (72*X^3 + 2664*X^2 + 23184*X + 43200)

theorem E33Theta_degree : E33Theta.natDegree = 4 := by
  unfold E33Theta
  compute_degree!

theorem E33Theta_coeff_four : E33Theta.coeff 4 = 81 := by
  simp only [E33Theta, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem E33Theta_primitive : E33Theta.IsPrimitive := by
  intro r hr
  have hd := ((C_dvd_iff_dvd_coeff _ _).mp hr) 4
  rw [E33Theta_coeff_four] at hd
  apply isUnit_of_dvd_unit hd
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))

theorem E33Theta_specialize : E33Theta.map (evalRingHom (3 : ℚ)) =
    C 27 * quartic.map (Int.castRingHom ℚ) := by
  simp only [E33Theta, quartic, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    coe_evalRingHom, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat, Polynomial.map_ofNat]
  norm_num [map_ofNat]
  ring

theorem E33Theta_irreducible : Irreducible E33Theta := by
  apply Rhone.Algebra.Galois.irreducible_of_map_of_isPrimitive
    (evalRingHom (3 : ℚ)) E33Theta_primitive
  · rw [E33Theta_specialize, E33Theta_degree]
    simp only [quartic, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_ofNat]
    compute_degree!
  · rw [E33Theta_specialize]
    exact (Rhone.Algebra.Galois.irreducible_C_mul_iff (by norm_num : (27 : ℚ) ≠ 0)).mpr
      quartic_rat_irreducible

noncomputable def E33U : Polynomial (RatFunc ℚ) :=
  E33Theta.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))

theorem E33U_irreducible : Irreducible E33U :=
  (E33Theta_primitive.irreducible_iff_irreducible_map_fraction_map).mp E33Theta_irreducible

theorem E33U_degree : E33U.natDegree = 4 := by
  rw [E33U, natDegree_map_eq_of_injective (IsFractionRing.injective _ _), E33Theta_degree]

theorem E33Theta_eq_E : E33Theta =
    Rhone.LinearAlgebra.Tridiag.E (Polynomial (Polynomial ℚ)) 3 3 X 0 (C X) := by
  rw [Rhone.LinearAlgebra.Tridiag.E_eq_cont]
  norm_num [Rhone.LinearAlgebra.Tridiag.cont, Rhone.LinearAlgebra.Tridiag.dcoef,
    Rhone.LinearAlgebra.Tridiag.bcoef, Rhone.LinearAlgebra.Tridiag.ccoef, E33Theta, map_ofNat]
  ring

end Rhone.Algebra.DiagonalIrreducibility
