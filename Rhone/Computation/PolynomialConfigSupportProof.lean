/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialConfigProof
public import Rhone.Computation.PolynomialSupportProof

/-! # Complete support bounds for the configuration polynomial -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

open Probability.Closure

theorem supported_factorA (p : Params) (i : Nat) : Supported (reflect (factorA p i)) 1 0 0 := by
  simp only [factorA, reflect, reflectList, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact (supported_monomial (0, 0, 0) _ 1 0 0 (by decide)).add
    (supported_monomial (1, 0, 0) _ 1 0 0 (by decide))

theorem supported_factorB (p : Params) (j : Nat) : Supported (reflect (factorB p j)) 0 1 0 := by
  simp only [factorB, reflect, reflectList, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact (supported_monomial (0, 0, 0) _ 0 1 0 (by decide)).add
    (supported_monomial (0, 1, 0) _ 0 1 0 (by decide))

theorem supported_factorAB (p : Params) (i j : Nat) :
    Supported (reflect (factorAB p i j)) 1 1 1 := by
  simp only [factorAB, reflect, reflectList, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact (supported_monomial (0, 0, 0) _ 1 1 1 (by decide)).add
    ((supported_monomial (1, 0, 0) _ 1 1 1 (by decide)).add
      ((supported_monomial (0, 1, 0) _ 1 1 1 (by decide)).add
        (supported_monomial (1, 1, 1) _ 1 1 1 (by decide))))

theorem supported_polynomial (p : Params) (c : Config) :
    Supported (reflect (polynomial p c)) (CheckerEncoding.decode c).nA
      (CheckerEncoding.decode c).nB (CheckerEncoding.decode c).t := by
  let ξ := CheckerEncoding.decode c
  have h := (((supported_factorA p 0).pow (ξ.a 0)).mul
      ((supported_factorA p 1).pow (ξ.a 1))).mul
      (((supported_factorB p 0).pow (ξ.b 0)).mul
        ((supported_factorB p 1).pow (ξ.b 1)))
  have hc := (((supported_factorAB p 0 0).pow (ξ.c 0 0)).mul
      ((supported_factorAB p 0 1).pow (ξ.c 0 1))).mul
      (((supported_factorAB p 1 0).pow (ξ.c 1 0)).mul
        ((supported_factorAB p 1 1).pow (ξ.c 1 1)))
  have hall := h.mul hc
  rw [reflect_polynomial]
  have hA0 := reflect_factorA p (0 : Fin 2)
  have hA1 := reflect_factorA p (1 : Fin 2)
  have hB0 := reflect_factorB p (0 : Fin 2)
  have hB1 := reflect_factorB p (1 : Fin 2)
  have hC00 := reflect_factorAB p (0 : Fin 2) (0 : Fin 2)
  have hC01 := reflect_factorAB p (0 : Fin 2) (1 : Fin 2)
  have hC10 := reflect_factorAB p (1 : Fin 2) (0 : Fin 2)
  have hC11 := reflect_factorAB p (1 : Fin 2) (1 : Fin 2)
  simp only [Fin.val_zero, Fin.val_one] at hA0 hA1 hB0 hB1 hC00 hC01 hC10 hC11
  rw [hA0, hA1, hB0, hB1, hC00, hC01, hC10, hC11] at hall
  simpa [Gcfg, Fin.prod_univ_two, Rhone.LinearAlgebra.Recursion.Config.nA,
    Rhone.LinearAlgebra.Recursion.Config.nB, Rhone.LinearAlgebra.Recursion.Config.sumA,
    Rhone.LinearAlgebra.Recursion.Config.sumB, Rhone.LinearAlgebra.Recursion.Config.t,
    Fin.sum_univ_two, ξ, Nat.add_assoc] using hall

end Rhone.Computation.PolynomialEncoding
