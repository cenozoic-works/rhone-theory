/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DiagonalObstruction.DeterminantNonzero
public import Rhone.Probability.SamplingUniform.RegularBlocks

/-! # Unconditional nonvanishing over the generic coefficient field -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform
open DiagonalChain LinearAlgebra.SlotDeletion SlotDeletion

abbrev GenericField := RatFunc (RatFunc ℚ)

noncomputable def genericTheta : GenericField := RatFunc.X

noncomputable def genericRho : GenericField := RatFunc.C (RatFunc.X : RatFunc ℚ)

theorem ED_ratFuncX_ne_zero {K : Type*} [Field K] [CharZero K]
    {m : ℕ} (hm : 1 ≤ m) (ρ : K) :
    ED m (RatFunc.X : RatFunc K) (RatFunc.C ρ) ≠ 0 := by
  have h := Analysis.DiagonalObstruction.E_mutationPolynomial_ne_zero hm ρ
  have hn := (RatFunc.algebraMap_injective K).ne h
  simpa only [map_zero, LinearAlgebra.Tridiag.E_map, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
    ED] using hn

theorem genericED_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    ED m genericTheta genericRho ≠ 0 :=
  ED_ratFuncX_ne_zero hm (RatFunc.X : RatFunc ℚ)

theorem genericLambdaE_ne_zero {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    LinearAlgebra.Tridiag.E (RatFunc GenericField) i j Algebra.SamplingUniform.lambdaA
        (Algebra.SamplingUniform.lambdaB genericTheta)
      (RatFunc.C genericRho) ≠ 0 :=
  lambdaE_ne_zero genericTheta genericRho (fun m hm => genericED_ne_zero m (by omega)) hi hj

theorem genericDfull_ne_zero (i j : ℕ) :
    Dfull (Algebra.SamplingUniform.lambdaA : RatFunc GenericField)
        (Algebra.SamplingUniform.lambdaB genericTheta)
      (RatFunc.C genericRho) i j ≠ 0 :=
  lambdaDfull_ne_zero genericTheta genericRho
    (fun m hm => genericED_ne_zero m (by omega)) i j

end Rhone.Probability.SamplingUniform
