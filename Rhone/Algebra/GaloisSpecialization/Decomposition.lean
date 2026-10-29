/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.RootReduction
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # A faithful decomposition group gives a residue-automorphism embedding -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial
open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] (p : A[X])

theorem separable_reduction_liesOver
    (hsep : (p.map (Ideal.Quotient.mk P)).Separable) :
    ((p.map (algebraMap A B)).map (Ideal.Quotient.mk Q)).Separable := by
  have hcomm : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (Ideal.Quotient.mk P) =
      (Ideal.Quotient.mk Q).comp (algebraMap A B) := by
    ext a
    exact Ideal.Quotient.algebraMap_mk_of_liesOver Q P a
  have h := hsep.map (f := algebraMap (A ⧸ P) (B ⧸ Q))
  rwa [Polynomial.map_map, hcomm, ← Polynomial.map_map] at h

variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    [FaithfulSMul G B] [IsDomain B] [Q.IsPrime]

theorem decomposition_injective_of_root_generated
    (hgen : Algebra.adjoin A {x : B | (p.map (algebraMap A B)).IsRoot x} = ⊤)
    (hsep : (p.map (Ideal.Quotient.mk P)).Separable) :
    Function.Injective (Ideal.Quotient.stabilizerHom Q P G) := by
  have hsB := separable_reduction_liesOver P Q p hsep
  intro σ τ hστ
  apply Subtype.ext
  apply (eq_of_smul_eq_smul (α := B))
  have he : MulSemiringAction.toAlgHom A B σ.val = MulSemiringAction.toAlgHom A B τ.val := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    change (p.map (algebraMap A B)).IsRoot x at hx
    have hσ : (p.map (algebraMap A B)).IsRoot (σ.val • x) := by
      rw [IsRoot.def, eval_map_algebraMap, aeval_smul]
      rw [IsRoot.def, eval_map_algebraMap] at hx
      rw [hx, smul_zero]
    have hτ : (p.map (algebraMap A B)).IsRoot (τ.val • x) := by
      rw [IsRoot.def, eval_map_algebraMap, aeval_smul]
      rw [IsRoot.def, eval_map_algebraMap] at hx
      rw [hx, smul_zero]
    have hred : Ideal.Quotient.mk Q (σ.val • x) = Ideal.Quotient.mk Q (τ.val • x) := by
      exact congrArg (fun f : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) => f (Ideal.Quotient.mk Q x)) hστ
    exact roots_eq_of_separable_specialization (Ideal.Quotient.mk Q) hsB hσ hτ hred
  intro x
  exact DFunLike.congr_fun he x

variable [Finite G] [Algebra.IsInvariant A B G]

noncomputable def decompositionEquivOfRootGenerated
    (hgen : Algebra.adjoin A {x : B | (p.map (algebraMap A B)).IsRoot x} = ⊤)
    (hsep : (p.map (Ideal.Quotient.mk P)).Separable) :
    MulAction.stabilizer G Q ≃* ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) :=
  MulEquiv.ofBijective (Ideal.Quotient.stabilizerHom Q P G)
    ⟨decomposition_injective_of_root_generated P Q p hgen hsep,
      Ideal.Quotient.stabilizerHom_surjective G P Q⟩

noncomputable def residueAutomorphismEmbedding
    (hgen : Algebra.adjoin A {x : B | (p.map (algebraMap A B)).IsRoot x} = ⊤)
    (hsep : (p.map (Ideal.Quotient.mk P)).Separable) :
    ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) →* G :=
  (MulAction.stabilizer G Q).subtype.comp
    (decompositionEquivOfRootGenerated (G := G) P Q p hgen hsep).symm.toMonoidHom

theorem residueAutomorphismEmbedding_injective
    (hgen : Algebra.adjoin A {x : B | (p.map (algebraMap A B)).IsRoot x} = ⊤)
    (hsep : (p.map (Ideal.Quotient.mk P)).Separable) :
    Function.Injective (residueAutomorphismEmbedding (G := G) P Q p hgen hsep) := by
  exact Subtype.val_injective.comp
    (decompositionEquivOfRootGenerated (G := G) P Q p hgen hsep).symm.injective

end Rhone.Algebra.GaloisSpecialization
