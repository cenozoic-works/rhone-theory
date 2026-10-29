/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.SamplingNumerator
public import Rhone.Probability.SamplingUniform.ResidueChain
public import Rhone.Probability.SamplingUniform.LambdaDenominator
public import Rhone.Algebra.SamplingUniform.InfinityCoefficient
public import Rhone.Probability.SamplingUniform.GenericField

/-! # The leading coefficient of the sampling numerator -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform
open LinearAlgebra.SlotDeletion SlotDeletion Analysis.RareAlleleHierarchy RareAlleleHierarchy
    DiagonalChain
variable {K : Type*}

noncomputable def lambdaFrequencyNumerator [CommRing K] (θ ρ : K) (m : ℕ) :
    MvPolynomial (Fin 2) (Polynomial K) :=
  samplingNumerator (MvPolynomial.C Polynomial.X)
    (MvPolynomial.C (Polynomial.C θ - Polynomial.X))
    (MvPolynomial.C (Polynomial.C ρ)) (MvPolynomial.X 0) (MvPolynomial.X 1) m

noncomputable def lambdaSamplingNumerator [CommRing K] (θ ρ : K) (m : ℕ) : Polynomial K :=
  cf 1 1 (samplingNumerator (MvPolynomial.C Polynomial.X)
    (MvPolynomial.C (Polynomial.C θ - Polynomial.X))
    (MvPolynomial.C (Polynomial.C ρ)) (MvPolynomial.X 0) (MvPolynomial.X 1) m)

variable [Field K] [CharZero K]

omit [CharZero K] in
@[simp] theorem evalAtInverse_C (c : K) :
    Algebra.SamplingUniform.evalAtInverse (Polynomial.C c) = RatFunc.C c := by
  simp [Algebra.SamplingUniform.evalAtInverse, Polynomial.coe_eval₂RingHom]

omit [CharZero K] in
@[simp] theorem evalAtInverse_X :
    Algebra.SamplingUniform.evalAtInverse (Polynomial.X : Polynomial K) =
        (Algebra.SamplingUniform.lambdaA : RatFunc K) := by
  simp [Algebra.SamplingUniform.evalAtInverse, Polynomial.coe_eval₂RingHom,
      Algebra.SamplingUniform.lambdaA]

omit [CharZero K] in
theorem evalAtInverse_complement (θ : K) :
    Algebra.SamplingUniform.evalAtInverse (Polynomial.C θ - Polynomial.X) =
        Algebra.SamplingUniform.lambdaB θ := by
  rw [map_sub, evalAtInverse_C, evalAtInverse_X]
  rfl

theorem lambdaDenominator_polynomial_ne_zero (θ ρ : K)
    (hE : ∀ k, 2 ≤ k → ED k θ ρ ≠ 0) (i j : ℕ) :
    Dfull (Polynomial.X : Polynomial K) (Polynomial.C θ - Polynomial.X)
      (Polynomial.C ρ) i j ≠ 0 := by
  intro hz
  have h := congrArg Algebra.SamplingUniform.evalAtInverse hz
  rw [Dfull_map] at h
  simp only [Algebra.SamplingUniform.evalAtInverse, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    map_sub, Polynomial.eval₂_C, map_zero] at h
  exact lambdaDfull_ne_zero θ ρ hE i j h

theorem lambdaFrequencyNumerator_map {R : Type*} [CommRing R]
    (φ : R →+* K) (θ ρ : R)
    (hE : ∀ k, 2 ≤ k → ED k (φ θ) (φ ρ) ≠ 0) (m : ℕ) :
    MvPolynomial.map (Polynomial.mapRingHom φ) (lambdaFrequencyNumerator θ ρ m) =
      lambdaFrequencyNumerator (φ θ) (φ ρ) m := by
  have hD : ∀ i j, Dfull (MvPolynomial.C (Polynomial.X : Polynomial K) :
      MvPolynomial (Fin 2) (Polynomial K))
      (MvPolynomial.C (Polynomial.C (φ θ) - Polynomial.X))
      (MvPolynomial.C (Polynomial.C (φ ρ))) i j ≠ 0 := by
    intro i j
    rw [← Dfull_map MvPolynomial.C]
    exact MvPolynomial.C_ne_zero.mpr
      (lambdaDenominator_polynomial_ne_zero (φ θ) (φ ρ) hE i j)
  unfold lambdaFrequencyNumerator
  rw [samplingNumerator_map]
  · simp only [MvPolynomial.map_C, MvPolynomial.map_X, Polynomial.coe_mapRingHom,
      Polynomial.map_X, Polynomial.map_sub, Polynomial.map_C]
  · simpa only [MvPolynomial.map_C, Polynomial.coe_mapRingHom,
      Polynomial.map_X, Polynomial.map_sub, Polynomial.map_C] using hD

theorem lambdaSamplingNumerator_map {R : Type*} [CommRing R]
    (φ : R →+* K) (θ ρ : R)
    (hE : ∀ k, 2 ≤ k → ED k (φ θ) (φ ρ) ≠ 0) (m : ℕ) :
    (lambdaSamplingNumerator θ ρ m).map φ =
      lambdaSamplingNumerator (φ θ) (φ ρ) m := by
  have h := congrArg (cf 1 1) (lambdaFrequencyNumerator_map φ θ ρ hE m)
  simpa only [cf, MvPolynomial.coeff_map, Polynomial.coe_mapRingHom,
    lambdaFrequencyNumerator, lambdaSamplingNumerator] using h

theorem lambdaSamplingNumerator_inverse (θ ρ : K)
    (hE : ∀ k, 2 ≤ k → ED k θ ρ ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    Algebra.SamplingUniform.evalAtInverse (lambdaSamplingNumerator θ ρ m) =
      Algebra.SamplingUniform.evalAtInverse (Dfull Polynomial.X (Polynomial.C θ - Polynomial.X)
        (Polynomial.C ρ) m m) * cf 1 1 (lambdaPhi θ ρ m m 0) := by
  have hD : ∀ i j, Dfull (MvPolynomial.C (Algebra.SamplingUniform.lambdaA : RatFunc K) :
      MvPolynomial (Fin 2) (RatFunc K))
      (MvPolynomial.C (Algebra.SamplingUniform.lambdaB θ)) (MvPolynomial.C (RatFunc.C ρ)) i j ≠ 0 :=
          by
    intro i j
    rw [← Dfull_map MvPolynomial.C]
    exact MvPolynomial.C_ne_zero.mpr (lambdaDfull_ne_zero θ ρ hE i j)
  have h := samplingNumerator_map
      (MvPolynomial.map (σ := Fin 2) Algebra.SamplingUniform.evalAtInverse)
    (MvPolynomial.C (Polynomial.X : Polynomial K))
    (MvPolynomial.C (Polynomial.C θ - Polynomial.X))
    (MvPolynomial.C (Polynomial.C ρ)) (MvPolynomial.X 0) (MvPolynomial.X 1)
    (by simpa only [MvPolynomial.map_C, evalAtInverse_X,
      evalAtInverse_C, evalAtInverse_complement] using hD) m
  have hc := congrArg (cf 1 1) h
  simp only [MvPolynomial.map_C, MvPolynomial.map_X, evalAtInverse_X,
    evalAtInverse_C, evalAtInverse_complement] at hc
  simp only [cf, MvPolynomial.coeff_map] at hc
  change Algebra.SamplingUniform.evalAtInverse (lambdaSamplingNumerator θ ρ m) =
    cf 1 1 (samplingNumerator (MvPolynomial.C Algebra.SamplingUniform.lambdaA)
      (MvPolynomial.C (Algebra.SamplingUniform.lambdaB θ)) (MvPolynomial.C (RatFunc.C ρ))
      (MvPolynomial.X 0) (MvPolynomial.X 1) m) at hc
  rw [generic_samplingNumerator_first_mixed Algebra.SamplingUniform.lambdaA
      (Algebra.SamplingUniform.lambdaB θ) (RatFunc.C ρ)
    (lambdaDfull_ne_zero θ ρ hE) hm] at hc
  rw [Dfull_map]
  simpa only [Algebra.SamplingUniform.evalAtInverse, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X,
    map_sub, Polynomial.eval₂_C, Algebra.SamplingUniform.lambdaA, Algebra.SamplingUniform.lambdaB,
        lambdaPhi] using hc

theorem lambdaSamplingNumerator_hasTop (θ ρ : K)
    (hE : ∀ k, 2 ≤ k → ED k θ ρ ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    SamplingNumerators.HasTop (lambdaSamplingNumerator θ ρ m)
      (lambdaDenominatorDegree m) (lambdaDenominatorConstant m * W m θ ρ) := by
  let r := regularTheta θ ρ hE m m 0
  have hr : (r : RatFunc K) = cf 1 1 (lambdaPhi θ ρ m m 0) := by
    simp only [r, coe_regularTheta, lambdaTheta, Theta_eq_cf11 _ _ _ hm hm]
  have he : Algebra.SamplingUniform.evalAtInverse
      (Dfull Polynomial.X (Polynomial.C θ - Polynomial.X)
      (Polynomial.C ρ) m m) * (r : RatFunc K) =
      Algebra.SamplingUniform.evalAtInverse (lambdaSamplingNumerator θ ρ m) := by
    rw [hr]
    exact (lambdaSamplingNumerator_inverse θ ρ hE hm).symm
  have hg := Dfull_lambda_hasTop θ ρ m
  refine ⟨Algebra.SamplingUniform.degree_le_of_regular_inverse_equation _ _ r hg.1 he, ?_⟩
  rw [Algebra.SamplingUniform.coeff_eq_of_regular_inverse_equation _ _ r hg.1 he, hg.2]
  have hres : frakE m θ ρ * Algebra.SamplingUniform.residueAtZero r = W m θ ρ := by
    change frakE m θ ρ * RatFunc.eval (RingHom.id K) 0
      (lambdaTheta θ ρ m m 0) = W m θ ρ
    exact lambdaTheta_residue_cleared θ ρ hE hm (Nat.zero_le m)
  rw [mul_assoc, hres]

theorem lambdaDenominatorConstant_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (m : ℕ) :
    φ (lambdaDenominatorConstant (K := R) m) =
      lambdaDenominatorConstant (K := S) m := by
  simp only [lambdaDenominatorConstant, map_mul, map_pow, map_neg, map_one,
    map_prod, map_sub, map_natCast]

theorem lambdaSamplingNumerator_mutation_coeff (ρ : K) {m : ℕ} (hm : 2 ≤ m) :
    (lambdaSamplingNumerator (Polynomial.X : Polynomial K) (Polynomial.C ρ) m).coeff
        (lambdaDenominatorDegree m) =
      Polynomial.C (lambdaDenominatorConstant (K := K) m) *
        W m Polynomial.X (Polynomial.C ρ) := by
  let φ := algebraMap (Polynomial K) (RatFunc K)
  have hE : ∀ k, 2 ≤ k → ED k (φ Polynomial.X) (φ (Polynomial.C ρ)) ≠ 0 := by
    intro k hk
    simpa only [φ, RatFunc.algebraMap_X, RatFunc.algebraMap_C] using
      ED_ratFuncX_ne_zero (by omega : 1 ≤ k) ρ
  apply RatFunc.algebraMap_injective K
  have hmap := lambdaSamplingNumerator_map φ Polynomial.X (Polynomial.C ρ) hE m
  have hcoeff := congrArg (fun f : Polynomial (RatFunc K) =>
    f.coeff (lambdaDenominatorDegree m)) hmap
  rw [Polynomial.coeff_map] at hcoeff
  rw [hcoeff, (lambdaSamplingNumerator_hasTop _ _ hE hm).2]
  rw [map_mul, W_map]
  congr 1
  simp only [RatFunc.algebraMap_C]
  exact (lambdaDenominatorConstant_map (RatFunc.C : K →+* RatFunc K) m).symm

end Rhone.Probability.SamplingUniform
