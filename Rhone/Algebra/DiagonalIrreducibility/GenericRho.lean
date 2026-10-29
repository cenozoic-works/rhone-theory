/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalIrreducibility.Generic
public import Rhone.Algebra.Galois.Small

/-! # E₃₃ is also irreducible over ℚ(θ) as a cubic in ρ -/

@[expose] public section

namespace Rhone.Algebra.DiagonalIrreducibility
open Polynomial

noncomputable def E33Rho : Polynomial (Polynomial ℚ) :=
  C (18*X+72)*X^3 + C (99*X^2+1062*X+2664)*X^2 +
  C (162*X^3+2754*X^2+14436*X+23184)*X +
  C (81*X^4+1836*X^3+14148*X^2+43200*X+43200)

theorem E33Rho_degree : E33Rho.natDegree = 3 := by
  unfold E33Rho
  compute_degree!
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) h
  norm_num [coeff_X] at hc

theorem E33Rho_coeff_three : E33Rho.coeff 3 = 18*X+72 := by
  simp only [E33Rho, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem E33Rho_coeff_one : E33Rho.coeff 1 = 162*X^3+2754*X^2+14436*X+23184 := by
  simp only [E33Rho, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem E33Rho_primitive : E33Rho.IsPrimitive := by
  intro r hr
  have hc := (C_dvd_iff_dvd_coeff _ _).mp hr
  have h : E33Rho.coeff 3 * (9*X^2+117*X+334) - E33Rho.coeff 1 = 864 := by
    rw [E33Rho_coeff_three, E33Rho_coeff_one]
    ring
  have hd : r ∣ (864:ℚ[X]) := h ▸ dvd_sub ((hc 3).mul_right _) (hc 1)
  apply isUnit_of_dvd_unit hd
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))

theorem E33Rho_specialize : E33Rho.map (evalRingHom (-13/3:ℚ)) =
    Rhone.Algebra.Galois.E33pt := by
  rw [Rhone.Algebra.Galois.E33pt_eq]
  simp only [E33Rho, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    coe_evalRingHom, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  norm_num [map_ofNat]
  ring

theorem E33Rho_irreducible : Irreducible E33Rho := by
  apply Rhone.Algebra.Galois.irreducible_of_map_of_isPrimitive
    (evalRingHom (-13/3:ℚ)) E33Rho_primitive
  · rw [E33Rho_specialize, Rhone.Algebra.Galois.natDegree_E33pt, E33Rho_degree]
  · rw [E33Rho_specialize]; exact Rhone.Algebra.Galois.E33pt_irreducible

theorem E33Rho_irreducible_ratFunc :
    Irreducible (E33Rho.map (algebraMap (Polynomial ℚ) (RatFunc ℚ))) :=
  (E33Rho_primitive.irreducible_iff_irreducible_map_fraction_map).mp E33Rho_irreducible

theorem E33Rho_eq_E : E33Rho =
    Rhone.LinearAlgebra.Tridiag.E (Polynomial (Polynomial ℚ)) 3 3 (C X) 0 X := by
  rw [Rhone.LinearAlgebra.Tridiag.E_eq_cont]
  norm_num [Rhone.LinearAlgebra.Tridiag.cont, Rhone.LinearAlgebra.Tridiag.dcoef,
    Rhone.LinearAlgebra.Tridiag.bcoef, Rhone.LinearAlgebra.Tridiag.ccoef, E33Rho, map_ofNat]
  ring

end Rhone.Algebra.DiagonalIrreducibility
