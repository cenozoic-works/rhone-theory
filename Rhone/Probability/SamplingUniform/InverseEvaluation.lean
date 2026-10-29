/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.ConstructionMap
public import Rhone.Probability.SamplingUniform.Generic
public import Rhone.Algebra.SamplingUniform.LambdaMatrix

/-! # Polynomial numerators under inverse-parameter evaluation -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open LinearAlgebra.SlotDeletion SlotDeletion Analysis.RareAlleleHierarchy RareAlleleHierarchy
variable {K : Type*} [Field K]

noncomputable def inverseEval : Polynomial K →+* RatFunc K :=
  Polynomial.eval₂RingHom RatFunc.C RatFunc.X⁻¹

noncomputable def lambdaDenominator (θ ρ : K) (i j : ℕ) : Polynomial K :=
  Dfull Polynomial.X (Polynomial.C θ - Polynomial.X) (Polynomial.C ρ) i j

noncomputable def lambdaNumerator (θ ρ : K) (i j t : ℕ) :
    MvPolynomial (Fin 2) (Polynomial K) :=
  clearedPhi (MvPolynomial.C Polynomial.X)
    (MvPolynomial.C (Polynomial.C θ - Polynomial.X)) (MvPolynomial.C (Polynomial.C ρ))
    kapX gamX kapY gamY i j t

noncomputable def mixedNumerator (θ ρ : K) (i j t : ℕ) : Polynomial K :=
  cf 1 1 (lambdaNumerator θ ρ i j t)

@[simp] theorem inverseEval_C (c : K) : inverseEval (Polynomial.C c) = RatFunc.C c := by
  simp [inverseEval]

@[simp] theorem inverseEval_X :
    inverseEval (Polynomial.X : Polynomial K) = (Algebra.SamplingUniform.lambdaA : RatFunc K) := by
  simp [inverseEval, Algebra.SamplingUniform.lambdaA]

theorem inverseEval_denominator (θ ρ : K) (i j : ℕ) :
    inverseEval (lambdaDenominator θ ρ i j) =
      Dfull (Algebra.SamplingUniform.lambdaA : RatFunc K) (Algebra.SamplingUniform.lambdaB θ)
          (RatFunc.C ρ) i j := by
  rw [lambdaDenominator, Dfull_map]
  simp only [map_sub, inverseEval_C, inverseEval_X, Algebra.SamplingUniform.lambdaB,
      Algebra.SamplingUniform.lambdaA]

theorem inverseEval_numerator (θ ρ : K)
    (hD : ∀ i j, Dfull (Algebra.SamplingUniform.lambdaA : RatFunc K)
        (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ) i j ≠ 0)
    (i j t : ℕ) :
    MvPolynomial.map inverseEval (lambdaNumerator θ ρ i j t) =
      clearedPhi (MvPolynomial.C Algebra.SamplingUniform.lambdaA)
          (MvPolynomial.C (Algebra.SamplingUniform.lambdaB θ))
        (MvPolynomial.C (RatFunc.C ρ)) kapX gamX kapY gamY i j t := by
  have hD' (x y : ℕ) : Dfull
      (MvPolynomial.C (Algebra.SamplingUniform.lambdaA : RatFunc K) : MvPolynomial (Fin 2)
          (RatFunc K))
      (MvPolynomial.C (Algebra.SamplingUniform.lambdaB θ)) (MvPolynomial.C (RatFunc.C ρ)) x y ≠ 0 :=
          by
    rw [← Dfull_map MvPolynomial.C]
    exact (MvPolynomial.C_ne_zero).mpr (hD x y)
  unfold lambdaNumerator
  rw [clearedPhi_map]
  · simp [map_sub, inverseEval_X, inverseEval_C, Algebra.SamplingUniform.lambdaA,
      Algebra.SamplingUniform.lambdaB,
      kapX, gamX, kapY, gamY]
  · intro x y
    simpa only [MvPolynomial.map_C, map_sub, inverseEval_C, inverseEval_X,
      Algebra.SamplingUniform.lambdaB, Algebra.SamplingUniform.lambdaA] using hD' x y

theorem inverseEval_mixedNumerator (θ ρ : K)
    (hD : ∀ i j, Dfull (Algebra.SamplingUniform.lambdaA : RatFunc K)
        (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ) i j ≠ 0)
    (i j t : ℕ) :
    inverseEval (mixedNumerator θ ρ i j t) =
      inverseEval (lambdaDenominator θ ρ i j) *
        cf 1 1 (genericPhi Algebra.SamplingUniform.lambdaA (Algebra.SamplingUniform.lambdaB θ)
            (RatFunc.C ρ) i j t) := by
  have h := congrArg (cf 1 1)
    (genericPhi_clear Algebra.SamplingUniform.lambdaA (Algebra.SamplingUniform.lambdaB θ)
        (RatFunc.C ρ) (hD i j) t)
  rw [cf_C_mul, ← inverseEval_numerator θ ρ hD] at h
  rw [inverseEval_denominator]
  exact h.symm

theorem genericPhi_mixed_eq_quotient (θ ρ : K)
    (hD : ∀ i j, Dfull (Algebra.SamplingUniform.lambdaA : RatFunc K)
        (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ) i j ≠ 0)
    (i j t : ℕ) :
    cf 1 1 (genericPhi Algebra.SamplingUniform.lambdaA (Algebra.SamplingUniform.lambdaB θ)
        (RatFunc.C ρ) i j t) =
      inverseEval (mixedNumerator θ ρ i j t) / inverseEval (lambdaDenominator θ ρ i j) := by
  rw [inverseEval_mixedNumerator θ ρ hD]
  exact (mul_div_cancel_left₀ _ (by rw [inverseEval_denominator]; exact hD i j)).symm

end Rhone.Probability.SamplingUniform
