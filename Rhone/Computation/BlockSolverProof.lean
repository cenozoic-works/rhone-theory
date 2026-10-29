/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.BlockSuccessProof
public import Rhone.Computation.BlockApplyProof
public import Rhone.Computation.BlockEntryProof

/-! # Total block solution and its finite specification -/

@[expose] public section

namespace Rhone.Computation

theorem solveBlock_eq_ok_spec (p : Params) (i j : Nat) (rhs : Array Rat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hij : 0 < i + j) :
    solveBlock p i j rhs = .ok (((List.range (min i j + 1)).map fun t =>
      (Rhone.LinearAlgebra.Tridiag.E Rat i j p.thetaA p.thetaB p.rho)⁻¹ *
        ∑ u ∈ Finset.range (min i j + 1),
          Rhone.LinearAlgebra.RecombinationExpansion.usmaniEntry
            (Rhone.LinearAlgebra.Tridiag.dcoef Rat i j p.thetaA p.thetaB p.rho)
            (Rhone.LinearAlgebra.Tridiag.bcoef Rat i j)
            (Rhone.LinearAlgebra.Tridiag.ccoef Rat p.rho) (min i j + 1) t u *
            rhs.getD u 0).toArray) := by
  rw [solveBlock_eq_ok p i j rhs hθA hθB hρ hij, applyBlockInverse_eq_toArray]
  congr 2
  apply List.map_congr_left
  intro t hmem
  have ht : t ≤ min i j := by have := List.mem_range.mp hmem; omega
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hmem'
  have hu : u ≤ min i j := by have := Finset.mem_range.mp hmem'; omega
  rw [blockInverseEntry_eq_usmani p i j t u ht hu, mul_assoc]

end Rhone.Computation
