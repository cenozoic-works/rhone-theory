/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ChainDenominator.GenericRational
public import Rhone.Probability.SamplingUniform.ResidueChain

/-! # The generic rational quotient is the low-frequency lambda residue -/

@[expose] public section

noncomputable section

namespace Rhone.Probability.ChainDenominator

open Polynomial DiagonalChain Algebra.SamplingUniform SamplingUniform Analysis.RareAlleleHierarchy
    RareAlleleHierarchy

def genericEval : (ℚ[X])[X] →+* RatFunc (RatFunc ℚ) :=
  (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))).comp
    (mapRingHom (algebraMap ℚ[X] (RatFunc ℚ)))

def genericTheta : RatFunc (RatFunc ℚ) := genericEval (C (X : ℚ[X]))

def genericRho : RatFunc (RatFunc ℚ) := genericEval X

theorem genericEval_W (k : ℕ) :
    W k genericTheta genericRho =
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (genericNumerator k) :=
  (W_map genericEval k (C (X : ℚ[X])) X).symm

theorem genericEval_frakE (k : ℕ) :
    frakE k genericTheta genericRho =
      algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (genericDenominator k) :=
  (frakE_map genericEval k (C (X : ℚ[X])) X).symm

theorem frakE_genericField_ne_zero (k : ℕ) : frakE k genericTheta genericRho ≠ 0 := by
  rw [genericEval_frakE]
  exact RatFunc.algebraMap_ne_zero (genericDenominator_ne_zero k)

theorem ED_genericField_ne_zero (k : ℕ) (hk : 2 ≤ k) : ED k genericTheta genericRho ≠ 0 := by
  intro hz
  apply frakE_genericField_ne_zero k
  exact Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩) hz

theorem lambda_residue_eq_genericQuotient (k : ℕ) (hk : 2 ≤ k) :
    RatFunc.eval (RingHom.id _) 0 (cf 1 1 (lambdaPhi genericTheta genericRho k k 0)) =
      genericQuotient k := by
  have h := lambdaPhi_cf11_residue genericTheta genericRho ED_genericField_ne_zero hk
  rw [genericEval_frakE, genericEval_W] at h
  apply (eq_div_iff (RatFunc.algebraMap_ne_zero (genericDenominator_ne_zero k))).mpr
  simpa only [mul_comm] using h

theorem lambda_residue_ne_zero (k : ℕ) (hk : 2 ≤ k) :
    RatFunc.eval (RingHom.id _) 0 (cf 1 1 (lambdaPhi genericTheta genericRho k k 0)) ≠ 0 := by
  rw [lambda_residue_eq_genericQuotient k hk]
  exact genericQuotient_ne_zero k hk

theorem lambda_residue_intDegree (k : ℕ) (hk : 2 ≤ k) :
    (RatFunc.eval (RingHom.id _) 0
      (cf 1 1 (lambdaPhi genericTheta genericRho k k 0))).intDegree = 2 - 2 * (k : ℤ) := by
  rw [lambda_residue_eq_genericQuotient k hk]
  exact genericQuotient_intDegree k hk

end Rhone.Probability.ChainDenominator
