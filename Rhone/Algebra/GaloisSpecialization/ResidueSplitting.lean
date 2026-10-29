/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.RootModel
public import Rhone.Algebra.GaloisSpecialization.Decomposition
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.RingTheory.Ideal.GoingUp

/-! # Constructing the specialized splitting field -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial
open scoped Pointwise

section RootModel

variable {A L : Type*} [CommRing A] [Field L] [Algebra A L]

theorem rootModel_splits (p : A[X]) (hsplit : (p.map (algebraMap A L)).Splits) :
    (p.map (algebraMap A (rootModel A L p))).Splits := by
  classical
  let B := rootModel A L p
  have hmap : (p.map (algebraMap A B)).map B.val.toRingHom =
      p.map (algebraMap A L) := by
    rw [Polynomial.map_map]
    rfl
  apply Splits.of_splits_map_of_injective (i := B.val.toRingHom) Subtype.val_injective
  · rwa [hmap]
  · intro x hx
    rw [hmap] at hx
    have hr : x ∈ p.rootSet L := by
      simpa only [rootSet_def, aroots_def, Finset.mem_coe, Multiset.mem_toFinset] using hx
    exact ⟨⟨x, Algebra.subset_adjoin hr⟩, rfl⟩

theorem rootModel_exists_maximal_liesOver [FaithfulSMul A L] {p : A[X]} (hp : p.Monic)
    (P : Ideal A) [P.IsMaximal] :
    ∃ Q : Ideal (rootModel A L p), Q.IsMaximal ∧ Q.LiesOver P := by
  have := rootModel_integral (L := L) hp
  have : FaithfulSMul A (rootModel A L p) :=
    (faithfulSMul_iff_algebraMap_injective A (rootModel A L p)).mpr fun a b hab =>
      FaithfulSMul.algebraMap_injective A L (congrArg (rootModel A L p).val hab)
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral P

end RootModel

section Quotient

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal A) (Q : Ideal B) [P.IsMaximal] [Q.IsMaximal] [Q.LiesOver P]

attribute [local instance] Ideal.Quotient.field

theorem isSplittingField_quotient_of_root_generated (p : A[X]) (hp : p.Monic)
    (hsplit : (p.map (algebraMap A B)).Splits)
    (hgen : Algebra.adjoin A {b : B | (p.map (algebraMap A B)).IsRoot b} = ⊤) :
    IsSplittingField (A ⧸ P) (B ⧸ Q) (p.map (Ideal.Quotient.mk P)) := by
  have hcomm : (Ideal.Quotient.mk Q).comp (algebraMap A B) =
      (algebraMap (A ⧸ P) (B ⧸ Q)).comp (Ideal.Quotient.mk P) := by
    ext a
    exact (Ideal.Quotient.algebraMap_mk_of_liesOver Q P a).symm
  have hmap : (p.map (algebraMap A B)).map (Ideal.Quotient.mk Q) =
      (p.map (Ideal.Quotient.mk P)).map (algebraMap (A ⧸ P) (B ⧸ Q)) := by
    rw [Polynomial.map_map, hcomm, ← Polynomial.map_map]
  constructor
  · rw [← hmap]
    exact hsplit.map _
  · let C := Algebra.adjoin (A ⧸ P) ((p.map (Ideal.Quotient.mk P)).rootSet (B ⧸ Q))
    apply _root_.Algebra.eq_top_iff.mpr
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hb : b ∈ Algebra.adjoin A {b : B | (p.map (algebraMap A B)).IsRoot b} :=
      hgen.symm ▸ Algebra.mem_top
    change Ideal.Quotient.mk Q b ∈ C
    induction hb using Algebra.adjoin_induction with
    | mem b hb =>
      apply Algebra.subset_adjoin
      apply (hp.map (Ideal.Quotient.mk P)).mem_rootSet.mpr
      change (p.map (algebraMap A B)).IsRoot b at hb
      have he := hb.map (f := Ideal.Quotient.mk Q)
      rw [hmap] at he
      simpa only [IsRoot.def, eval_map_algebraMap] using he
    | algebraMap a =>
      rw [← Ideal.Quotient.algebraMap_mk_of_liesOver Q P a]
      exact C.algebraMap_mem (Ideal.Quotient.mk P a)
    | add b c _ _ hb hc =>
      rw [map_add]
      exact C.add_mem hb hc
    | mul b c _ _ hb hc =>
      rw [map_mul]
      exact C.mul_mem hb hc

end Quotient

end Rhone.Algebra.GaloisSpecialization
