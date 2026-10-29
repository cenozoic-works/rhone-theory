/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ParamsProof
public import Rhone.Probability.ExplicitFormula.Block
public import Mathlib.Algebra.Order.Field.Rat

/-! # Mathematical laws used by the finite hierarchy invariant -/

@[expose] public section

namespace Rhone.Computation

structure HierarchyValueLaws (p : Params) (value : Nat → Nat → Nat → Rat) : Prop where
  empty : value 0 0 0 = 1
  block : ∀ i j t, 0 < i + j → t ≤ min i j →
    value i j t = (Rhone.LinearAlgebra.Tridiag.E Rat i j p.thetaA p.thetaB p.rho)⁻¹ *
      ∑ u ∈ Finset.range (min i j + 1),
        Rhone.LinearAlgebra.RecombinationExpansion.usmaniEntry
          (Rhone.LinearAlgebra.Tridiag.dcoef Rat i j p.thetaA p.thetaB p.rho)
          (Rhone.LinearAlgebra.Tridiag.bcoef Rat i j)
          (Rhone.LinearAlgebra.Tridiag.ccoef Rat p.rho) (min i j + 1) t u *
          Rhone.Probability.ExplicitFormula.srcR
            (p.piA.getD 0 0 * p.piA.getD 1 0) (p.piA.getD 1 0 - p.piA.getD 0 0)
            (p.piB.getD 0 0 * p.piB.getD 1 0) (p.piB.getD 1 0 - p.piB.getD 0 0)
            value i j u

theorem hierarchyValueLaws_of_solution (p : Params)
    (q : Rhone.LinearAlgebra.Recursion.Config 2 2 → Rat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hq : Rhone.LinearAlgebra.Recursion.IsSolution p.thetaA p.thetaB p.rho
      (fun i : Fin 2 => p.piA.getD i.val 0) (fun j : Fin 2 => p.piB.getD j.val 0) q)
    (hπA : (∑ i : Fin 2, p.piA.getD i.val 0) = 1)
    (hπB : (∑ j : Fin 2, p.piB.getD j.val 0) = 1) :
    HierarchyValueLaws p (Rhone.Probability.Multilinear.Phi q
      (fun i : Fin 2 => p.piA.getD i.val 0) (fun j : Fin 2 => p.piB.getD j.val 0)) := by
  refine ⟨Rhone.Probability.SlotDeletion.Phi_zero_zero hq 0, ?_⟩
  intro i j t hij ht
  have hπA' : p.piA.getD 0 0 + p.piA.getD 1 0 = 1 := by
    simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one] using hπA
  have hπB' : p.piB.getD 0 0 + p.piB.getD 1 0 = 1 := by
    simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one] using hπB
  have hblock := Rhone.Probability.ExplicitFormula.Phi_block hθA hθB hρ hq hπA' hπB' hij ht
  simpa only [Probability.ExplicitFormula.phiRecursionSource_eq_srcR,
    Probability.Multilinear.kap, Probability.Multilinear.gam,
    Fin.val_zero, Fin.val_one] using hblock

end Rhone.Computation
