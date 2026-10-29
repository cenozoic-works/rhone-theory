/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.BackwardContinuantProof
public import Rhone.Computation.RangeProductIntervalProof
public import Rhone.Analysis.RecombinationExpansion.Continuant
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring

/-! # Executable inverse entries and Usmani's formula -/

@[expose] public section

namespace Rhone.Computation

private theorem upperCoefficient (i j t u : Nat) (htu : t ≤ u)
    (hui : u ≤ i) (huj : u ≤ j) :
    ((2 ^ (u - t) * rangeProduct (i - u) (i - t) *
      rangeProduct (j - u) (j - t) : Nat) : Rat) =
      (2 : Rat) ^ (u - t) *
        ∏ s ∈ Finset.Ico t u, (((i - s) * (j - s) : Nat) : Rat) := by
  rw [rangeProduct_sub_eq_prod i t u htu hui, rangeProduct_sub_eq_prod j t u htu huj]
  push_cast
  rw [Finset.prod_mul_distrib]
  ring

private theorem lowerCoefficient (u t : Nat) :
    (rangeProduct u t : Rat) = ∏ s ∈ Finset.Ico u t, ((s : Rat) + 1) := by
  rw [rangeProduct_eq_prod_succ]
  simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_one]

theorem blockInverseEntry_eq_usmani (p : Params) (i j t u : Nat)
    (ht : t ≤ min i j) (hu : u ≤ min i j) :
    blockInverseEntry p i j
      (forwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j + 1))
      (backwardContinuants (blockDiagonal p i j) (blockBeta p i j) (min i j))
      (1 / Rhone.LinearAlgebra.Tridiag.E Rat i j p.thetaA p.thetaB p.rho) t u =
      (Rhone.LinearAlgebra.Tridiag.E Rat i j p.thetaA p.thetaB p.rho)⁻¹ *
        Rhone.LinearAlgebra.RecombinationExpansion.usmaniEntry
          (Rhone.LinearAlgebra.Tridiag.dcoef Rat i j p.thetaA p.thetaB p.rho)
          (Rhone.LinearAlgebra.Tridiag.bcoef Rat i j)
          (Rhone.LinearAlgebra.Tridiag.ccoef Rat p.rho) (min i j + 1) t u := by
  by_cases htu : t ≤ u
  · rw [blockInverseEntry, ite_eq_left htu,
      forwardContinuants_eq_cont p i j (min i j + 1) t le_rfl (by omega),
      backwardContinuants_eq_Qc p i j (u + 1) (by omega),
      upperCoefficient i j t u htu (le_trans hu (min_le_left _ _))
        (le_trans hu (min_le_right _ _)),
      Rhone.Analysis.RecombinationExpansion.usmaniEntry_T_of_le i j p.thetaA p.thetaB p.rho htu]
    simp only [one_div]
    ring
  · have hut : u ≤ t := by omega
    rw [blockInverseEntry, ite_eq_right htu,
      forwardContinuants_eq_cont p i j (min i j + 1) u le_rfl (by omega),
      backwardContinuants_eq_Qc p i j (t + 1) (by omega), lowerCoefficient,
      Rhone.Analysis.RecombinationExpansion.usmaniEntry_T_of_ge i j p.thetaA p.thetaB p.rho hut]
    simp only [one_div]
    ring

end Rhone.Computation
