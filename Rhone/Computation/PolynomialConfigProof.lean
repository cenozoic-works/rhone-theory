/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialFactorProof
public import Rhone.Computation.CheckerEncodingProof

/-! # The executable configuration polynomial is the protected generating function -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

open Probability.Closure

theorem polynomial_eq_fold (p : Params) (c : Config) :
    polynomial p c =
      (List.range 2).foldl (fun out i =>
        (List.range 2).foldl (fun out j =>
          (List.range (c.c.getD (2 * i + j) 0)).foldl
            (fun out _ => mulPoly out (factorAB p i j)) out) out)
        ((List.range 2).foldl (fun out j =>
          (List.range (c.b.getD j 0)).foldl
            (fun out _ => mulPoly out (factorB p j)) out)
          ((List.range 2).foldl (fun out i =>
            (List.range (c.a.getD i 0)).foldl
              (fun out _ => mulPoly out (factorA p i)) out) #[((0, 0, 0), 1)])) := by
  simp [polynomial, factorA, factorB, factorAB,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range_eq_range']

theorem reflect_polynomial (p : Params) (c : Config) :
    reflect (polynomial p c) =
      Gcfg (fun i : Fin 2 => p.piA.getD i.val 0)
        (fun j : Fin 2 => p.piB.getD j.val 0) (CheckerEncoding.decode c) := by
  rw [polynomial_eq_fold]
  simp only [show List.range 2 = [0, 1] from rfl, List.foldl_cons,
    List.foldl_nil, reflect_repeat, reflect_one, one_mul]
  simp only [Gcfg, Fin.prod_univ_two, CheckerEncoding.decode, Fin.val_zero, Fin.val_one]
  have hA0 := reflect_factorA p (0 : Fin 2)
  have hA1 := reflect_factorA p (1 : Fin 2)
  have hB0 := reflect_factorB p (0 : Fin 2)
  have hB1 := reflect_factorB p (1 : Fin 2)
  have hC00 := reflect_factorAB p (0 : Fin 2) (0 : Fin 2)
  have hC01 := reflect_factorAB p (0 : Fin 2) (1 : Fin 2)
  have hC10 := reflect_factorAB p (1 : Fin 2) (0 : Fin 2)
  have hC11 := reflect_factorAB p (1 : Fin 2) (1 : Fin 2)
  simp only [Fin.val_zero, Fin.val_one] at hA0 hA1 hB0 hB1 hC00 hC01 hC10 hC11
  rw [hA0, hA1, hB0, hB1, hC00, hC01, hC10, hC11]
  simp only [mul_assoc]

end Rhone.Computation.PolynomialEncoding
