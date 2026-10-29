/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.PoleTransfer
public import Rhone.Algebra.SamplingUniform.RealSpecialization
public import Rhone.Algebra.Rational.Solve
public import Rhone.Algebra.Rational.Map
public import Rhone.Algebra.BoundedDenominator

/-! # No formula of any bounded degree equals the sampling probability -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open Polynomial LinearAlgebra.Recursion LinearAlgebra.SlotDeletion SlotDeletion DiagonalChain

theorem ringHom_injective_of_field {F S : Type*} [Field F] [Semiring S] [Nontrivial S]
    (f : F →+* S) : Function.Injective f :=
  f.injective

section Injective

variable {K : Type*} [Field K]

theorem swapLocal_injective : Function.Injective (Algebra.SamplingUniform.swapLocal (K := K)) := by
  intro a b h
  apply (Polynomial.Bivariate.swap (R := K)).injective
  exact Polynomial.map_injective _ (RatFunc.algebraMap_injective K) h

theorem nestedLocalization_injective :
    Function.Injective (Algebra.SamplingUniform.nestedLocalization (K := K)) := by
  intro a b h
  have h1 : Polynomial.map (Algebra.SamplingUniform.swapLocal (K := RatFunc K))
      (Algebra.SamplingUniform.frequencyEquiv ((RatFunc K)[X])
          (MvPolynomial.map Algebra.SamplingUniform.swapLocal a)) =
      Polynomial.map (Algebra.SamplingUniform.swapLocal (K := RatFunc K))
        (Algebra.SamplingUniform.frequencyEquiv ((RatFunc K)[X])
            (MvPolynomial.map Algebra.SamplingUniform.swapLocal b)) :=
    swapLocal_injective h
  have h2 := Polynomial.map_injective _ swapLocal_injective h1
  have h3 := (Algebra.SamplingUniform.frequencyEquiv ((RatFunc K)[X])).injective h2
  exact MvPolynomial.map_injective _ swapLocal_injective h3

theorem samplingMutationDenominator_ne_zero [CharZero K] (ρ : K) (m : ℕ) :
    samplingMutationDenominator ρ m ≠ 0 := by
  intro h
  have h0 : MvPolynomial.C (σ := Fin 2)
      (Dfull X (C (X : K[X]) - X) (C (C ρ)) m m) = 0 :=
    nestedLocalization_injective (by rw [map_zero]; exact h)
  have h1 : Dfull X (C (X : K[X]) - X) (C (C ρ)) m m = 0 :=
    MvPolynomial.C_injective (Fin 2) _ (by rw [h0, map_zero])
  have ht := (Dfull_lambda_hasTop (X : K[X]) (C ρ) m).2
  rw [h1, coeff_zero] at ht
  have hne : lambdaDenominatorConstant (K := K[X]) m * frakE m (X : K[X]) (C ρ) ≠ 0 := by
    apply mul_ne_zero (lambdaDenominatorConstant_ne_zero m)
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact Analysis.DiagonalObstruction.E_mutationPolynomial_ne_zero
      (by have := (Finset.mem_Icc.mp hk).1; omega) ρ
  exact hne ht.symm

end Injective

abbrev UniformBase := RatFunc ℚ

abbrev UniformCoefficient := RatFunc (RatFunc (RatFunc UniformBase))

abbrev UniformPolynomial := Polynomial UniformCoefficient

abbrev UniformField := RatFunc UniformCoefficient

noncomputable def uniformLambda : UniformCoefficient :=
  RatFunc.C (RatFunc.C (RatFunc.X : RatFunc UniformBase))

noncomputable def uniformA : UniformField :=
  algebraMap UniformPolynomial UniformField (C uniformLambda)

noncomputable def uniformB : UniformField :=
  algebraMap UniformPolynomial UniformField (X - C uniformLambda)

noncomputable def uniformRho : UniformField :=
  algebraMap UniformPolynomial UniformField
      (C (Algebra.SamplingUniform.nestedConstant (RatFunc.X : UniformBase)))

noncomputable def uniformP : UniformField :=
  algebraMap UniformPolynomial UniformField (C (RatFunc.X : UniformCoefficient))

noncomputable def uniformR : UniformField :=
  algebraMap UniformPolynomial UniformField
    (C (RatFunc.C (RatFunc.X : RatFunc (RatFunc UniformBase))))

noncomputable def uniformSamplingValue (m : ℕ) : UniformField :=
  algebraMap UniformPolynomial UniformField
      (samplingMutationNumerator (RatFunc.X : UniformBase) m) /
    algebraMap UniformPolynomial UniformField
      (samplingMutationDenominator (RatFunc.X : UniformBase) m)

theorem piOf_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : R) :
    (fun i => φ (piOf p i)) = piOf (φ p) := by
  funext i
  fin_cases i <;> simp [piOf]

theorem exists_uniform_real_point :
    ∃ ι : UniformField →+* ℝ, 0 < ι uniformA ∧ 0 < ι uniformB ∧ 0 ≤ ι uniformRho := by
  obtain ⟨ι, hρ, hl, hθ⟩ := Algebra.SamplingUniform.exists_real_specialization
  refine ⟨ι, ?_, ?_, ?_⟩
  · rw [uniformA, RatFunc.algebraMap_C]
    exact hl
  · rw [uniformB, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_sub]
    exact sub_pos.mpr hθ
  · rw [uniformRho, RatFunc.algebraMap_C]
    exact hρ.le

theorem uniform_detNeZero :
    Algebra.Rational.DetNeZero uniformA uniformB uniformRho (piOf uniformP) (piOf uniformR) := by
  obtain ⟨ι, hA, hB, hR⟩ := exists_uniform_real_point
  intro N
  exact Algebra.Rational.det_bMat_ne_zero_of_hom ι hA hB hR N

theorem existsUnique_uniform_solution :
    ∃! q : Config 2 2 → UniformField,
      IsSolution uniformA uniformB uniformRho (piOf uniformP) (piOf uniformR) q :=
  ⟨Algebra.Rational.qOfDet uniform_detNeZero, Algebra.Rational.qOfDet_isSolution uniform_detNeZero,
    fun _ hq => Algebra.Rational.qOfDet_unique uniform_detNeZero hq⟩

theorem uniformSamplingValue_eq_of_isSolution {q : Config 2 2 → UniformField}
    (hq : IsSolution uniformA uniformB uniformRho (piOf uniformP) (piOf uniformR) q)
    (m : ℕ) : q (samplingMM m) = uniformSamplingValue m := by
  obtain ⟨ι, hA, hB, hR⟩ := exists_uniform_real_point
  have hq' : IsSolution (ι uniformA) (ι uniformB) (ι uniformRho)
      (piOf (ι uniformP)) (piOf (ι uniformR)) (fun η => ι (q η)) := by
    have h := Algebra.Rational.isSolution_map ι hq
    rwa [piOf_map, piOf_map] at h
  let ψ : UniformPolynomial →+* ℝ := ι.comp (algebraMap UniformPolynomial UniformField)
  let φ : MvPolynomial (Fin 2) (Polynomial (Polynomial UniformBase)) →+* ℝ :=
    ψ.comp Algebra.SamplingUniform.nestedLocalization
  have hφA : φ (MvPolynomial.C X) = ι uniformA := by
    change ι (algebraMap UniformPolynomial UniformField
      (Algebra.SamplingUniform.nestedLocalization (MvPolynomial.C X))) = _
    rw [Algebra.SamplingUniform.nestedLocalization_lambda]
    rfl
  have hφB : φ (MvPolynomial.C (C X - X)) = ι uniformB := by
    change ι (algebraMap UniformPolynomial UniformField
      (Algebra.SamplingUniform.nestedLocalization (MvPolynomial.C (C X - X)))) = _
    rw [map_sub MvPolynomial.C, map_sub Algebra.SamplingUniform.nestedLocalization,
        Algebra.SamplingUniform.nestedLocalization_theta,
      Algebra.SamplingUniform.nestedLocalization_lambda]
    rfl
  have hφR : φ (MvPolynomial.C (C (C RatFunc.X))) = ι uniformRho := by
    change ι (algebraMap UniformPolynomial UniformField
      (Algebra.SamplingUniform.nestedLocalization (MvPolynomial.C (C (C RatFunc.X))))) = _
    rw [Algebra.SamplingUniform.nestedLocalization_scalar]
    rfl
  have hφp : φ (MvPolynomial.X 0) = ι uniformP := by
    change ι (algebraMap UniformPolynomial UniformField
      (Algebra.SamplingUniform.nestedLocalization (MvPolynomial.X 0))) = _
    rw [Algebra.SamplingUniform.nestedLocalization_p]
    rfl
  have hφr : φ (MvPolynomial.X 1) = ι uniformR := by
    change ι (algebraMap UniformPolynomial UniformField
      (Algebra.SamplingUniform.nestedLocalization (MvPolynomial.X 1))) = _
    rw [Algebra.SamplingUniform.nestedLocalization_r]
    rfl
  have hnum := map_samplingNumerator_eq_Dfull_mul_q hA hB hR hq' φ (MvPolynomial.C X)
    (MvPolynomial.C (C X - X)) (MvPolynomial.C (C (C RatFunc.X)))
    (MvPolynomial.X 0) (MvPolynomial.X 1) hφA hφB hφR hφp hφr m
  have hden : ψ (samplingMutationDenominator (RatFunc.X : UniformBase) m) =
      Dfull (ι uniformA) (ι uniformB) (ι uniformRho) m m := by
    have h := Dfull_map (φ.comp MvPolynomial.C) X (C X - X) (C (C RatFunc.X)) m m
    simp only [RingHom.comp_apply] at h hφA hφB hφR
    rw [hφA, hφB, hφR] at h
    exact h
  have hnum' : ψ (samplingMutationNumerator (RatFunc.X : UniformBase) m) =
      ψ (samplingMutationDenominator (RatFunc.X : UniformBase) m) * ι (q (samplingMM m)) := by
    rw [hden]
    exact hnum
  have key : algebraMap UniformPolynomial UniformField
        (samplingMutationNumerator (RatFunc.X : UniformBase) m) =
      algebraMap UniformPolynomial UniformField
        (samplingMutationDenominator (RatFunc.X : UniformBase) m) * q (samplingMM m) := by
    apply ringHom_injective_of_field ι
    rw [map_mul]
    exact hnum'
  rw [uniformSamplingValue, eq_div_iff
    (Rhone.Algebra.algebraMap_ne_zero
      (samplingMutationDenominator_ne_zero (RatFunc.X : UniformBase) m)), key, mul_comm]

theorem no_uniform_expression_uniformSamplingValue (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Rhone.Algebra.Expr UniformCoefficient,
      Rhone.Algebra.DAdm uniformA uniformB uniformRho D e ∧
      Rhone.Algebra.Expr.eval uniformA uniformB uniformRho e = uniformSamplingValue m := by
  obtain ⟨m, hm, G, hirr, hdiv, hn, hdeg⟩ :=
    DiagonalObstruction.unbounded_surviving_E_mm_factor_degree D
  refine ⟨m, hm, ?_⟩
  rintro ⟨e, hadm, heval⟩
  have hG := Algebra.SamplingUniform.irreducible_map_nestedConstant G hirr
  have hden : G.map Algebra.SamplingUniform.nestedConstant ∣ (uniformSamplingValue m).denom := by
    apply Rhone.Algebra.prime_dvd_denom (samplingMutationDenominator_ne_zero _ m) rfl hG.prime
    · exact surviving_factor_dvd_samplingMutationDenominator RatFunc.X hm hdiv
    · exact surviving_factor_not_dvd_samplingMutationNumerator RatFunc.X hm hirr hn
  have hbound := Rhone.Algebra.natDegree_le_of_dvd_denom_eval
      (Rhone.Algebra.boundedDen_of_poly D (C uniformLambda))
    (Rhone.Algebra.boundedDen_of_poly D (X - C uniformLambda))
    (Rhone.Algebra.boundedDen_of_poly D
        (C (Algebra.SamplingUniform.nestedConstant (RatFunc.X : UniformBase))))
    hadm hG (by
      change G.map Algebra.SamplingUniform.nestedConstant ∣
        (Rhone.Algebra.Expr.eval uniformA uniformB uniformRho e).denom
      rw [heval]
      exact hden)
  rw [Algebra.SamplingUniform.natDegree_map_nestedConstant] at hbound
  omega

theorem no_bounded_degree_formula_sampling (D : ℕ) {q : Config 2 2 → UniformField}
    (hq : IsSolution uniformA uniformB uniformRho (piOf uniformP) (piOf uniformR) q) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Rhone.Algebra.Expr UniformCoefficient,
      Rhone.Algebra.DAdm uniformA uniformB uniformRho D e ∧
      Rhone.Algebra.Expr.eval uniformA uniformB uniformRho e = q (samplingMM m) := by
  obtain ⟨m, hm, h⟩ := no_uniform_expression_uniformSamplingValue D
  exact ⟨m, hm, (uniformSamplingValue_eq_of_isSolution hq m) ▸ h⟩

end Rhone.Probability.SamplingUniform
