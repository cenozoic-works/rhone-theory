/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialConfigSupportProof
public import Rhone.Computation.PolynomialAssemblyProof
public import Rhone.Probability.SlotDeletion.Surj
public import Mathlib.Algebra.Order.Field.Rat

/-! # Configuration assembly agrees with the coefficient expansion of `q` -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

open Probability.Closure LinearAlgebra.Multilinear Probability.Multilinear
    LinearAlgebra.SlotDeletion Probability.SlotDeletion

theorem q_eq_sum_coeff_mul_phi (p : Params) (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hπA : (∑ i : Fin 2, p.piA.getD i.val 0) = 1)
    (hπB : (∑ j : Fin 2, p.piB.getD j.val 0) = 1) :
    Rhone.LinearAlgebra.Recursion.q
      (πA := fun k : Fin 2 => p.piA.getD k.val 0)
      (πB := fun k : Fin 2 => p.piB.getD k.val 0) hθA hθB hρ ξ =
      ∑ i ∈ Finset.range (ξ.nA + 1), ∑ j ∈ Finset.range (ξ.nB + 1),
        ∑ t ∈ Finset.range (ξ.t + 1),
          (Gcfg (fun k : Fin 2 => p.piA.getD k.val 0)
            (fun k : Fin 2 => p.piB.getD k.val 0) ξ).coeff (exponent (i, j, t)) *
          Phi (Rhone.LinearAlgebra.Recursion.q
      (πA := fun k : Fin 2 => p.piA.getD k.val 0)
      (πB := fun k : Fin 2 => p.piB.getD k.val 0) hθA hθB hρ)
            (fun k : Fin 2 => p.piA.getD k.val 0)
            (fun k : Fin 2 => p.piB.getD k.val 0) i j t := by
  have h := q_xi_eq_sum_Gcfg_coeff_mul_Phi
    (πA := fun k : Fin 2 => p.piA.getD k.val 0)
    (πB := fun k : Fin 2 => p.piB.getD k.val 0)
    hθA hθB hρ (Rhone.LinearAlgebra.Recursion.q_isSolution hθA hθB hρ)
    (by simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one] using hπA)
    (by simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one] using hπB)
    (matchOf ξ) isMatching_matchOf (alphaOf ξ) (betaOf ξ)
  simpa only [xi_matchOf, exponent] using h

theorem assemble_polynomial_eq_q (p : Params) (c : Config) (tab : PhiTable)
    (ha : c.a.size = 2) (hb : c.b.size = 2) (hc : c.c.size = 4)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hπA : (∑ i : Fin 2, p.piA.getD i.val 0) = 1)
    (hπB : (∑ j : Fin 2, p.piB.getD j.val 0) = 1)
    (htab : ∀ i j t, i ≤ c.block.1 → j ≤ c.block.2 → t ≤ min i j →
      tab.get i j t = Phi (Rhone.LinearAlgebra.Recursion.q
      (πA := fun k : Fin 2 => p.piA.getD k.val 0)
      (πB := fun k : Fin 2 => p.piB.getD k.val 0) hθA hθB hρ)
        (fun k : Fin 2 => p.piA.getD k.val 0)
        (fun k : Fin 2 => p.piB.getD k.val 0) i j t) :
    assemble tab (polynomial p c) =
      Rhone.LinearAlgebra.Recursion.q
      (πA := fun k : Fin 2 => p.piA.getD k.val 0)
      (πB := fun k : Fin 2 => p.piB.getD k.val 0) hθA hθB hρ (CheckerEncoding.decode c) := by
  have hblock : c.block = ((CheckerEncoding.decode c).nA, (CheckerEncoding.decode c).nB) := by
    calc c.block = (CheckerEncoding.encode (CheckerEncoding.decode c)).block :=
        congrArg Config.block (CheckerEncoding.encode_decode c ha hb hc).symm
      _ = _ := CheckerEncoding.encode_block _
  rw [assemble_eq_momentSum]
  rw [momentSum_congr (supported_polynomial p c) _
    (Phi (Rhone.LinearAlgebra.Recursion.q
      (πA := fun k : Fin 2 => p.piA.getD k.val 0)
      (πB := fun k : Fin 2 => p.piB.getD k.val 0) hθA hθB hρ)
      (fun k : Fin 2 => p.piA.getD k.val 0) (fun k : Fin 2 => p.piB.getD k.val 0))
    (by simpa only [hblock] using htab)]
  rw [momentSum_eq_triple (supported_polynomial p c), reflect_polynomial]
  exact (q_eq_sum_coeff_mul_phi p (CheckerEncoding.decode c) hθA hθB hρ hπA hπB).symm

end Rhone.Computation.PolynomialEncoding
