/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Algebra
public import Rhone.Probability.SamplingNumerators.Lambda

/-! # Generic noncancellation of the `(3,3)` determinant in the sampling numerator -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators
open Polynomial DiagonalChain Algebra.DiagonalIrreducibility

abbrev MutationSumField := RatFunc ℚ
abbrev RecombinationPolynomial := Polynomial MutationSumField
abbrev LambdaPolynomial := Polynomial RecombinationPolynomial

noncomputable def determinant33 : RecombinationPolynomial := ED 3 (C RatFunc.X) X
noncomputable def genericNumerator : LambdaPolynomial :=
  samplingNumerator X (C (C RatFunc.X) - X) (C X)
noncomputable def genericDenominator : LambdaPolynomial :=
  d33 X (C (C RatFunc.X) - X) (C X)

theorem E33_lambda :
    LinearAlgebra.Tridiag.E LambdaPolynomial 3 3 X (C (C RatFunc.X) - X) (C X) = C determinant33 :=
        by
  rw [determinant33, ED, LinearAlgebra.Tridiag.E_map]
  apply Analysis.DenominatorEquation.E_indep_of_theta
  simp only [map_zero]
  ring

theorem determinant33_eq_map : determinant33 =
    E33Rho.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
  rw [E33Rho_eq_E]
  have h := LinearAlgebra.Tridiag.E_map
    (mapRingHom (algebraMap (Polynomial ℚ) (RatFunc ℚ))) 3 3 (C X) 0 X
  simpa [determinant33, ED, RatFunc.algebraMap_X] using h.symm

theorem determinant33_prime : Prime determinant33 := by
  rw [determinant33_eq_map]
  exact E33Rho_irreducible_ratFunc.prime

theorem determinant33_not_dvd_n33 :
    ¬ C determinant33 ∣ n33 (X : LambdaPolynomial) (C (C RatFunc.X) - X) (C X) 0 := by
  apply constant_prime_not_dvd_of_coeff 10 determinant33_prime.not_isUnit
  rw [n33_lambda_coeff_ten]
  apply IsCoprime.neg_left
  have h := Sharpness.chain_three_isCoprime_map
    (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (IsFractionRing.injective _ _)
  change IsCoprime
    ((mapRingHom (algebraMap (Polynomial ℚ) (RatFunc ℚ))) (W 3 (C X) X))
    ((mapRingHom (algebraMap (Polynomial ℚ) (RatFunc ℚ))) (ED 3 (C X) X)) at h
  rw [W_map, ED_map] at h
  simpa [determinant33, RatFunc.algebraMap_X] using h

theorem determinant33_not_dvd_genericNumerator :
    ¬ C determinant33 ∣ genericNumerator := by
  unfold genericNumerator samplingNumerator
  rw [E33_lambda]
  apply not_dvd_unit_mul_add
  · exact (isUnit_iff_ne_zero.mpr (by norm_num : (4/729 : ℚ) ≠ 0)).map (algebraMap ℚ _)
  · exact determinant33_not_dvd_n33

theorem determinant33_dvd_genericDenominator : C determinant33 ∣ genericDenominator := by
  unfold genericDenominator d33
  rw [E33_lambda]
  exact dvd_mul_left _ _

theorem generic_sampling33_denominator_contains
    {F : Type*} [Field F] (ι : LambdaPolynomial →+* F) (hι : Function.Injective ι)
    {v : F} (hv : ι genericNumerator = ι genericDenominator * v)
    (d n : LambdaPolynomial) (hd : ι d * v = ι n) : C determinant33 ∣ d := by
  exact prime_dvd_clearing ι hι (Polynomial.prime_C_iff.mpr determinant33_prime)
    determinant33_dvd_genericDenominator determinant33_not_dvd_genericNumerator hv hd

end Rhone.Probability.SamplingNumerators
