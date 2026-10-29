/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.GenericCoordinates.GenericField
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Mutation coordinates and the canonical-to-generic ring equivalence -/

@[expose] public section

namespace Rhone.Analysis.GenericCoordinates

open Polynomial _root_.Algebra

local instance ratioFieldScalarTower :
    @IsScalarTower ℚ RatioField GenericField Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable def mutationCoordinates : Fin 2 → GenericField := ![thetaA, thetaB]

theorem mutationCoordinates_adjoin_eq_top :
    IntermediateField.adjoin ℚ (Set.range mutationCoordinates) = ⊤ := by
  let I := IntermediateField.adjoin ℚ (Set.range mutationCoordinates)
  have ha : thetaA ∈ I := IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩
  have hb : thetaB ∈ I := IntermediateField.subset_adjoin _ _ ⟨1, rfl⟩
  have hs : sigmaVariable ∈ I := by rw [variable_eq_thetaA_inv]; exact I.inv_mem ha
  have hr : ratioIn ∈ I := by rw [ratioIn_eq_thetaB_div_thetaA]; exact I.div_mem hb ha
  have hbase : ∀ p : Polynomial ℚ,
      algebraMap RatioField GenericField (algebraMap (Polynomial ℚ) RatioField p) ∈ I := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using I.add_mem hp hq
    | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
      refine I.mul_mem ?_ (I.pow_mem ?_ n)
      · have h := RingHom.congr_fun (RingHom.ext_rat
          ((algebraMap RatioField GenericField).comp ((algebraMap ℚ[X] RatioField).comp C))
          (algebraMap ℚ GenericField)) c
        simp only [RingHom.comp_apply] at h
        rw [h]
        exact I.algebraMap_mem c
      · change ratioIn ∈ I
        exact hr
  have hscalar : ∀ c : RatioField, algebraMap RatioField GenericField c ∈ I := by
    intro c
    obtain ⟨p, q, _, hpq⟩ := IsFractionRing.div_surjective (Polynomial ℚ) c
    rw [← hpq, map_div₀]
    exact I.div_mem (hbase p) (hbase q)
  have hpoly : ∀ p : Polynomial RatioField,
      algebraMap (Polynomial RatioField) GenericField p ∈ I := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using I.add_mem hp hq
    | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      refine I.mul_mem ?_ (I.pow_mem hs n)
      simpa only [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply] using hscalar c
  apply top_unique
  intro x _
  obtain ⟨p, q, _, hpq⟩ := IsFractionRing.div_surjective (Polynomial RatioField) x
  rw [← hpq]
  exact I.div_mem (hpoly p) (hpoly q)

theorem transcendental_fraction_variable (k : Type*) [Field k] :
    Transcendental k (algebraMap (Polynomial k) (FractionRing (Polynomial k)) X) := by
  rw [transcendental_algebraMap_iff
    (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k)))]
  exact Polynomial.transcendental_X k

theorem mutationCoordinates_algebraicIndependent :
    AlgebraicIndependent ℚ mutationCoordinates := by
  have hr : AlgebraicIndependent ℚ (fun _ : Unit => ratio) := by
    rw [algebraicIndependent_unique_type_iff]
    convert transcendental_fraction_variable ℚ
    · exact Subsingleton.elim _ _
    · rfl
  have hs : AlgebraicIndependent RatioField (fun _ : Unit => sigmaVariable) := by
    rw [algebraicIndependent_unique_type_iff]
    exact transcendental_fraction_variable RatioField
  have hpair := hr.sumElim_comp hs
  have hdegree : Cardinal.mk (Fin 2) ≤ trdeg ℚ GenericField := by
    simpa using hpair.cardinalMk_le_trdeg
  let S := Algebra.adjoin ℚ (Set.range mutationCoordinates)
  let : IsFractionRing S GenericField := IsFractionRing.of_field _ _ fun x => by
    have hx : x ∈ IntermediateField.adjoin ℚ (Set.range mutationCoordinates) := by
      rw [mutationCoordinates_adjoin_eq_top]
      trivial
    obtain ⟨p, hp, q, hq, hpq⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
    exact ⟨⟨p, hp⟩, ⟨q, hq⟩, hpq⟩
  let : Algebra.IsAlgebraic S GenericField :=
    IsLocalization.isAlgebraic GenericField (nonZeroDivisors S)
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite
    ℚ mutationCoordinates hdegree).1

noncomputable def canonicalToGeneric : FractionRing (MvPolynomial (Fin 2) ℚ) →+* GenericField :=
  IsFractionRing.lift
    (algebraicIndependent_iff_injective_aeval.mp mutationCoordinates_algebraicIndependent)

theorem canonicalToGeneric_injective : Function.Injective canonicalToGeneric :=
  canonicalToGeneric.injective

@[simp] theorem canonicalToGeneric_variable (i : Fin 2) :
    canonicalToGeneric
      (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
        (MvPolynomial.X i)) = mutationCoordinates i := by
  rw [canonicalToGeneric, IsFractionRing.lift_algebraMap]
  exact MvPolynomial.aeval_X mutationCoordinates i

section CanonicalRing

noncomputable local instance (priority := high) fracAlgebra {ι : Type*} {F : Type*} [Field F] :
    Algebra F (FractionRing (MvPolynomial ι F)) := inferInstance

noncomputable def canonicalRingEquiv : FractionRing (MvPolynomial (Fin 2) ℚ) ≃+* GenericField :=
  (mutationCoordinates_algebraicIndependent.aevalEquivField.trans
    ((IntermediateField.equivOfEq mutationCoordinates_adjoin_eq_top).trans
      IntermediateField.topEquiv)).toRingEquiv

theorem canonicalRingEquiv_eq :
    (canonicalRingEquiv : FractionRing (MvPolynomial (Fin 2) ℚ) → GenericField)
      = canonicalToGeneric := by
  funext x
  exact mutationCoordinates_algebraicIndependent.aevalEquivField_apply_coe x

end CanonicalRing

noncomputable def canonicalEquivGeneric :
    FractionRing (MvPolynomial (Fin 2) ℚ) ≃ₐ[ℚ] GenericField :=
  AlgEquiv.ofRingEquiv (f := canonicalRingEquiv) (fun r => by simp only [eq_ratCast, map_ratCast])

theorem canonicalToGeneric_surjective : Function.Surjective canonicalToGeneric := by
  rw [← canonicalRingEquiv_eq]
  exact canonicalRingEquiv.surjective

end Rhone.Analysis.GenericCoordinates
