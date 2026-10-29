/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.FieldComparison
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Specialization through a surjective algebra homomorphism -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

variable {k A K L G : Type*} [Field k] [CommRing A] [Algebra k A]
    [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [Group G] [Finite G] [MulSemiringAction G L]
    [IsGaloisGroup G K L]

attribute [local instance] Ideal.Quotient.field

theorem exists_algebra_specialization_embedding (φ : A →ₐ[k] k) (p : A[X])
    [IsSplittingField K L (p.map (algebraMap A K))]
    (hlc : φ p.leadingCoeff ≠ 0) (hsep : (p.map φ.toRingHom).Separable) :
    ∃ f : (p.map φ.toRingHom).Gal →* G, Function.Injective f := by
  classical
  have hsurj : Function.Surjective φ := fun x =>
    ⟨algebraMap k A x, φ.commutes x⟩
  let P := RingHom.ker φ.toRingHom
  have : P.IsMaximal := RingHom.ker_isMaximal_of_surjective φ.toRingHom hsurj
  let e : (A ⧸ P) ≃ₐ[k] k := Ideal.quotientKerAlgEquivOfSurjective hsurj
  have hsurj₀ : Function.Surjective (algebraMap k (A ⧸ P)) := by
    intro x
    refine ⟨e x, e.injective ?_⟩
    exact e.commutes (e x)
  have he (x : A) : e (Ideal.Quotient.mk P x) = φ x :=
    Ideal.quotientKerAlgEquivOfSurjective_mk hsurj x
  have hpoly : (p.map φ.toRingHom).map (algebraMap k (A ⧸ P)) =
      p.map (Ideal.Quotient.mk P) := by
    ext n
    simp only [coeff_map]
    apply e.injective
    rw [he, e.commutes]
    rfl
  have hlc₀ : Ideal.Quotient.mk P p.leadingCoeff ≠ 0 := by
    intro hz
    apply hlc
    rw [← he, hz, map_zero]
  have hsep₀ : (p.map (Ideal.Quotient.mk P)).Separable := hpoly ▸ hsep.map
  obtain ⟨j, hj⟩ := exists_specialization_embedding (K := K) (L := L) (G := G)
    p P hlc₀ hsep₀
  let q := p.map (Ideal.Quotient.mk P)
  let M := q.SplittingField
  have : IsSplittingField (A ⧸ P) M
      ((p.map φ.toRingHom).map (algebraMap k (A ⧸ P))) := by
    rw [hpoly]
    infer_instance
  have : IsSplittingField k M (p.map φ.toRingHom) :=
    isSplittingField_of_surjective_base hsurj₀ _
  let d : M ≃ₐ[k] (p.map φ.toRingHom).SplittingField :=
    IsSplittingField.algEquiv M (p.map φ.toRingHom)
  let c := (AlgEquiv.autCongr d).symm.trans
    (AlgEquiv.extendScalarsHomOfSurjective (A := M) hsurj₀)
  exact ⟨j.comp c.toMonoidHom, hj.comp c.injective⟩

end Rhone.Algebra.GaloisSpecialization
