/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialPowerProof
public import Mathlib.Algebra.Order.Field.Rat

/-! # Configuration factors denote the protected generating factors -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

open Probability.Closure Probability.SlotDeletion

def factorA (p : Params) (i : Nat) : Poly :=
  #[((0, 0, 0), p.piA.getD i 0), ((1, 0, 0), if i == 0 then 1 else -1)]

def factorB (p : Params) (j : Nat) : Poly :=
  #[((0, 0, 0), p.piB.getD j 0), ((0, 1, 0), if j == 0 then 1 else -1)]

def factorAB (p : Params) (i j : Nat) : Poly :=
  let sa : Rat := if i == 0 then 1 else -1
  let sb : Rat := if j == 0 then 1 else -1
  #[((0, 0, 0), p.piA.getD i 0 * p.piB.getD j 0),
    ((1, 0, 0), sa * p.piB.getD j 0),
    ((0, 1, 0), p.piA.getD i 0 * sb), ((1, 1, 1), sa * sb)]

theorem sign_eq_eps (i : Fin 2) :
    (if i.val == 0 then 1 else -1 : Rat) = eps Rat i := by
  fin_cases i <;> rfl

theorem reflect_factorA (p : Params) (i : Fin 2) :
    reflect (factorA p i.val) = gA (fun k : Fin 2 => p.piA.getD k.val 0) i := by
  fin_cases i <;> simp [factorA, reflect, reflectList, gA,
    exponent, mono3, MvPolynomial.X]

theorem reflect_factorB (p : Params) (j : Fin 2) :
    reflect (factorB p j.val) = gB (fun k : Fin 2 => p.piB.getD k.val 0) j := by
  fin_cases j <;> simp [factorB, reflect, reflectList, gB,
    exponent, mono3, MvPolynomial.X]

theorem reflect_factorAB (p : Params) (i j : Fin 2) :
    reflect (factorAB p i.val j.val) =
      gAB (fun k : Fin 2 => p.piA.getD k.val 0)
        (fun k : Fin 2 => p.piB.getD k.val 0) i j := by
  simp only [factorAB, reflect, reflectList, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, sign_eq_eps]
  rw [gAB, MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.C_mul_X_eq_monomial]
  have hxyz : (MvPolynomial.X 0 : MvPolynomial (Fin 3) Rat) *
      MvPolynomial.X 1 * MvPolynomial.X 2 = MvPolynomial.monomial (mono3 1 1 1) 1 := by
    simpa using X_pow_prod_eq_monomial (F := Rat) 1 1 1
  rw [hxyz, MvPolynomial.C_mul_monomial, mul_one]
  simp [exponent, mono3, add_assoc]

end Rhone.Computation.PolynomialEncoding
