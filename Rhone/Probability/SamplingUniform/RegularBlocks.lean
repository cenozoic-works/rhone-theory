/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.SamplingUniform.LambdaMatrix
public import Rhone.Probability.SamplingUniform.EdgesAtZero
public import Rhone.Probability.DiagonalChain.Cleared

/-! # Nonsingularity of every block after the inverse-parameter substitution -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform
open Matrix LinearAlgebra.SlotDeletion SlotDeletion DiagonalChain
variable {K : Type*} [Field K]

theorem lambdaBlock_eq_poleMatrix (i j : ℕ) (θ ρ : K) :
    LinearAlgebra.Tridiag.T (RatFunc K) i j Algebra.SamplingUniform.lambdaA
        (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ) =
      Algebra.SamplingUniform.poleMatrix ((i : K) - (j : K))
          ((LinearAlgebra.Tridiag.T K i j 0 θ ρ).map Algebra.SamplingUniform.regularC) := by
  rw [Algebra.SamplingUniform.lambdaBlock_split]
  unfold Algebra.SamplingUniform.poleMatrix Algebra.SamplingUniform.constantBlock
  simp only [div_eq_mul_inv, Matrix.map_map]
  rfl

theorem lambdaE_off_diagonal_ne_zero [CharZero K] {i j : ℕ} (hij : i ≠ j) (θ ρ : K) :
    LinearAlgebra.Tridiag.E (RatFunc K) i j Algebra.SamplingUniform.lambdaA
        (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ) ≠ 0 := by
  rw [LinearAlgebra.Tridiag.E, lambdaBlock_eq_poleMatrix]
  exact Algebra.SamplingUniform.poleMatrix_det_ne_zero
      (Algebra.SamplingUniform.index_difference_ne_zero hij) _

theorem lambdaE_ne_zero [CharZero K] (θ ρ : K)
    (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0) {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    LinearAlgebra.Tridiag.E (RatFunc K) i j Algebra.SamplingUniform.lambdaA
        (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ) ≠ 0 := by
  by_cases hij : i = j
  · subst j
    rw [LinearAlgebra.Tridiag.E, Algebra.SamplingUniform.lambdaBlock_diagonal]
    have hn := (map_ne_zero (RatFunc.C : K →+* RatFunc K)).mpr (hE i hi)
    simpa only [ED, LinearAlgebra.Tridiag.E, RingHom.map_det, RingHom.mapMatrix_apply] using hn
  · exact lambdaE_off_diagonal_ne_zero hij θ ρ

theorem lambdaDfull_ne_zero [CharZero K] (θ ρ : K)
    (hE : ∀ m, 2 ≤ m → ED m θ ρ ≠ 0) (i j : ℕ) :
    Dfull (Algebra.SamplingUniform.lambdaA : RatFunc K) (Algebra.SamplingUniform.lambdaB θ)
        (RatFunc.C ρ) i j ≠ 0 := by
  unfold Dfull
  apply mul_ne_zero
  · exact mul_ne_zero (poch_inverseMutation_ne_zero i)
      (poch_complementaryMutation_ne_zero θ j)
  · unfold Erect
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    exact lambdaE_ne_zero θ ρ hE (Finset.mem_Ico.mp hp).1 (Finset.mem_Ico.mp hs).1

end Rhone.Probability.SamplingUniform
