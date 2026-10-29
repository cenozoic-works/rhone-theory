/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalIrreducibility.GenericRho
public import Rhone.Probability.Sharpness.PoleTransfer
public import Rhone.Algebra.BoundedDenominator

/-! # Complementary recombination-degree obstruction for the k=3 diagonal chain -/

@[expose] public section

namespace Rhone.Probability.DiagonalIrreducibility
open Polynomial DiagonalChain Analysis.RareAlleleHierarchy RareAlleleHierarchy

theorem three_le_of_rho_chain {D : ℕ} {e : Algebra.Expr (RatFunc ℚ)}
    {v : ℕ → ℕ → RatFunc (RatFunc ℚ)}
    (hv : IsDiagChain
      (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) (C RatFunc.X))
      (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) X) v)
    (he : Algebra.DAdm
      (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) (C RatFunc.X)) 0
      (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) X) D e)
    (heval : Algebra.Expr.eval
      (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) (C RatFunc.X)) 0
      (algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ)) X) e = v 3 0) : 3 ≤ D := by
  let j := algebraMap (Polynomial ℚ) (RatFunc ℚ)
  let ι := algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ))
  have hj : Function.Injective j := IsFractionRing.injective _ _
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have hz : Algebra.BoundedDen D (0 : RatFunc (RatFunc ℚ)) := by
    simpa using (Algebra.boundedDen_of_poly D (0 : Polynomial (RatFunc ℚ)))
  obtain ⟨N, M, _, hNM, hbound⟩ :=
    Algebra.boundedDen_eval (Algebra.boundedDen_of_poly D (C RatFunc.X)) hz
        (Algebra.boundedDen_of_poly D X) he
  have hchain : IsDiagChain (ι (C (j X))) (ι X) v := by
    simpa [j, ι, RatFunc.algebraMap_X] using hv
  have hpole := Rhone.Probability.Sharpness.chain_three_denominator_contains
    j hj ι hι v hchain M N (by
      rw [heval] at hNM
      simpa [ι, mul_comm] using hNM)
  have hE : Algebra.DiagonalIrreducibility.E33Rho.map j = ED 3 (C (j X)) X := by
    rw [Algebra.DiagonalIrreducibility.E33Rho_eq_E]
    have h := Rhone.LinearAlgebra.Tridiag.E_map (mapRingHom j) 3 3 (C X) 0 X
    simpa [ED] using h
  have hi : Irreducible (Algebra.DiagonalIrreducibility.E33Rho.map j) :=
      Algebra.DiagonalIrreducibility.E33Rho_irreducible_ratFunc
  have hd := hbound (Algebra.DiagonalIrreducibility.E33Rho.map j) hi (by rw [hE]; exact hpole)
  rwa [natDegree_map_eq_of_injective hj, Algebra.DiagonalIrreducibility.E33Rho_degree] at hd

end Rhone.Probability.DiagonalIrreducibility
