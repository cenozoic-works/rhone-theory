/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.Normalization

/-! # Galois specialization without a monicity restriction -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial

variable {A K L G : Type*} [CommRing A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]

attribute [local instance] Ideal.Quotient.field

theorem exists_specialization_embedding (p : A[X])
    [IsSplittingField K L (p.map (algebraMap A K))]
    (P : Ideal A) [P.IsMaximal]
    (hlc : Ideal.Quotient.mk P p.leadingCoeff ≠ 0)
    (hsep : (p.map (Ideal.Quotient.mk P)).Separable) :
    ∃ f : (p.map (Ideal.Quotient.mk P)).Gal →* G, Function.Injective f := by
  classical
  have hp : p ≠ 0 := by
    intro hz
    simp [hz] at hlc
  have hlcK : algebraMap A K p.leadingCoeff ≠ 0 := by
    intro hz
    have h : p.leadingCoeff = 0 := IsFractionRing.injective A K
      (show algebraMap A K p.leadingCoeff = algebraMap A K 0 by
        rw [map_zero]
        exact hz)
    exact (leadingCoeff_ne_zero.mpr hp) h
  have : IsSplittingField K L (p.integralNormalization.map (algebraMap A K)) := by
    rw [← integralNormalization_map (algebraMap A K) p hlcK]
    exact isSplittingField_integralNormalization _
      (by simpa only [Polynomial.map_zero] using
        (Polynomial.map_injective (algebraMap A K) (IsFractionRing.injective A K)).ne hp)
  have hnorm : (p.map (Ideal.Quotient.mk P)).integralNormalization =
      p.integralNormalization.map (Ideal.Quotient.mk P) :=
    integralNormalization_map (Ideal.Quotient.mk P) p hlc
  obtain ⟨j, hj⟩ := exists_monic_specialization_embedding (K := K) (L := L) (G := G)
    p.integralNormalization (monic_integralNormalization hp) P
    (hnorm ▸ separable_integralNormalization hsep)
  let p₀ := p.map (Ideal.Quotient.mk P)
  let q₀ := p.integralNormalization.map (Ideal.Quotient.mk P)
  have : IsSplittingField (A ⧸ P) p₀.SplittingField q₀ := by
    change IsSplittingField (A ⧸ P) p₀.SplittingField
      (p.integralNormalization.map (Ideal.Quotient.mk P))
    rw [← hnorm]
    exact isSplittingField_integralNormalization p₀ hsep.ne_zero
  let e : p₀.SplittingField ≃ₐ[A ⧸ P] q₀.SplittingField :=
    IsSplittingField.algEquiv p₀.SplittingField q₀
  let c : p₀.Gal ≃* q₀.Gal := AlgEquiv.autCongr e
  exact ⟨j.comp c.toMonoidHom, hj.comp c.injective⟩

end Rhone.Algebra.GaloisSpecialization
