/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.ModelAction
public import Rhone.Algebra.GaloisSpecialization.ResidueSplitting
public import Mathlib.FieldTheory.Galois.IsGaloisGroup

/-! # Galois specialization for monic polynomials over an integrally closed domain -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial
open scoped Pointwise

variable {A K L G : Type*} [CommRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] Ideal.Quotient.field

theorem exists_monic_specialization_embedding (p : A[X]) (hp : p.Monic)
    [IsSplittingField K L (p.map (algebraMap A K))]
    (P : Ideal A) [P.IsMaximal] (hsep : (p.map (Ideal.Quotient.mk P)).Separable) :
    ∃ f : (p.map (Ideal.Quotient.mk P)).Gal →* G, Function.Injective f := by
  classical
  have : FaithfulSMul G L := IsGaloisGroup.faithful K
  have : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).mpr (by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K))
  have : SMulCommClass G A L := ⟨fun g a x => by
    simp only [Algebra.smul_def]
    rw [smul_mul', IsScalarTower.algebraMap_apply A K L, smul_algebraMap]⟩
  have hroots : (p.map (algebraMap A K)).rootSet L = p.rootSet L := by
    simp only [Polynomial.rootSet, Polynomial.aroots, Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq]
  have hgenL : Algebra.adjoin K (p.rootSet L) = ⊤ := by
    rw [← hroots]
    exact IsSplittingField.adjoin_rootSet L (p.map (algebraMap A K))
  have hsplitL : (p.map (algebraMap A L)).Splits := by
    have h := IsSplittingField.splits L (p.map (algebraMap A K))
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h
  let B := rootModel A L p
  have : FaithfulSMul G B := rootModel_faithful (G := G) p hgenL
  have : Algebra.IsInvariant A B G := rootModel_invariant (K := K) (G := G) p hp
  obtain ⟨Q, hQmax, hQlies⟩ := rootModel_exists_maximal_liesOver (L := L) hp P
  have := hQmax
  have := hQlies
  have : IsSplittingField (A ⧸ P) (B ⧸ Q) (p.map (Ideal.Quotient.mk P)) :=
    isSplittingField_quotient_of_root_generated P Q p hp
      (rootModel_splits p hsplitL) (rootModel_generated_by_roots p)
  let e : (B ⧸ Q) ≃ₐ[A ⧸ P] (p.map (Ideal.Quotient.mk P)).SplittingField :=
    IsSplittingField.algEquiv (B ⧸ Q) (p.map (Ideal.Quotient.mk P))
  let c : (p.map (Ideal.Quotient.mk P)).Gal ≃* ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) :=
    AlgEquiv.autCongr e.symm
  let j := residueAutomorphismEmbedding (G := G) P Q p
    (rootModel_generated_by_roots p) hsep
  exact ⟨j.comp c.toMonoidHom,
    (residueAutomorphismEmbedding_injective P Q p
      (rootModel_generated_by_roots p) hsep).comp c.injective⟩

end Rhone.Algebra.GaloisSpecialization
