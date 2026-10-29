/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationDegree.SpectralDegree
public import Rhone.Analysis.DiagonalObstruction.Unbounded

/-! # Unbounded recombination degree of the distinguished spectral factors -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open Polynomial MvPolynomial Algebra.DiagonalObstruction Analysis.DiagonalObstruction

theorem unbounded_distinguished_recombination_degree (D : ℕ) :
    ∃ m : ℕ, ∃ F : Polynomial (Polynomial ℤ),
      2 ≤ m ∧ F.Monic ∧ F ∣ spectralPolynomial m ∧ 0 ∈ factorLabels m F ∧
      Irreducible (rationalFunctionFactor F) ∧ D < (coordinates ℤ F).degreeOf 1 := by
  obtain ⟨m, F, hm, hmon, hdiv, hzero, hirr, _, hdeg⟩ :=
    exists_irreducible_distinguished_factor_gt (D + 1)
  refine ⟨m, F, hm, hmon, hdiv, hzero, hirr, ?_⟩
  rw [rationalFunctionFactor_natDegree F hmon] at hdeg
  have h := spectral_factor_degree_transfer hm hdiv
  omega

end Rhone.Probability.RecombinationDegree
