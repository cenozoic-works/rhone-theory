/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisIrreducibility.Bridge
public import Rhone.Algebra.GaloisIrreducibility.Normal
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.SplittingField.Construction

/-! # A normal subgroup of a full symmetric Galois group keeps `f` irreducible -/

@[expose] public section

namespace Rhone.Algebra.GaloisIrreducibility

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (p : F[X])

def rootPerm (σ : E ≃ₐ[F] E) : Equiv.Perm (p.rootSet E) where
  toFun := Set.MapsTo.restrict _ _ _ (Polynomial.rootSet_mapsTo (p := p) σ.toAlgHom)
  invFun := Set.MapsTo.restrict _ _ _ (Polynomial.rootSet_mapsTo (p := p) σ.symm.toAlgHom)
  left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : E))
  right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : E))

@[simp]
theorem rootPerm_coe (σ : E ≃ₐ[F] E) (x : p.rootSet E) :
    ((rootPerm p σ x : E)) = σ (x : E) := rfl

def rootPermHom : (E ≃ₐ[F] E) →* Equiv.Perm (p.rootSet E) where
  toFun := rootPerm p
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

@[simp]
theorem rootPermHom_coe (σ : E ≃ₐ[F] E) (x : p.rootSet E) :
    ((rootPermHom p σ x : E)) = σ (x : E) := rfl

theorem rootPermHom_injective [Polynomial.IsSplittingField F E p] :
    Function.Injective (rootPermHom (E := E) p) := by
  intro σ τ h
  have hx : Set.EqOn (σ.toAlgHom : E →ₐ[F] E) (τ.toAlgHom : E →ₐ[F] E) (p.rootSet E) := by
    intro x hx
    have h2 := congrArg (fun π => ((π ⟨x, hx⟩ : p.rootSet E) : E)) h
    simpa using h2
  have h3 : (σ.toAlgHom : E →ₐ[F] E) = (τ.toAlgHom : E →ₐ[F] E) :=
    AlgHom.ext_of_adjoin_eq_top (Polynomial.IsSplittingField.adjoin_rootSet E p) hx
  exact AlgEquiv.ext fun x => DFunLike.congr_fun h3 x

theorem exists_mem_rootPerm_eq {H : Subgroup (E ≃ₐ[F] E)} [H.Normal]
    (hsurj : Function.Surjective (rootPermHom (E := E) p))
    (hH : H.map (rootPermHom p) ≠ ⊥) (x y : p.rootSet E) :
    ∃ σ ∈ H, σ (x : E) = (y : E) := by
  have : (H.map (rootPermHom p)).Normal := ‹H.Normal›.map _ hsurj
  obtain ⟨π, hπ, hxy⟩ := exists_mem_apply_eq hH x y
  obtain ⟨σ, hσH, rfl⟩ := Subgroup.mem_map.mp hπ
  exact ⟨σ, hσH, congrArg Subtype.val hxy⟩

theorem exists_mem_rootPerm_eq_of_ne_bot [Polynomial.IsSplittingField F E p]
    {H : Subgroup (E ≃ₐ[F] E)} [H.Normal]
    (hsurj : Function.Surjective (rootPermHom (E := E) p)) (hH : H ≠ ⊥) (x y : p.rootSet E) :
    ∃ σ ∈ H, σ (x : E) = (y : E) := by
  refine exists_mem_rootPerm_eq p hsurj ?_ x y
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective H (rootPermHom_injective p)]
  exact hH

theorem irreducible_map_fixedField [Polynomial.IsSplittingField F E p]
    (hsep : p.Separable) (hdeg : p.natDegree ≠ 0)
    (hsurj : Function.Surjective (rootPermHom (E := E) p))
    {H : Subgroup (E ≃ₐ[F] E)} [H.Normal] (hH : H ≠ ⊥) :
    Irreducible (p.map (algebraMap F (IntermediateField.fixedField H))) := by
  classical
  set K := IntermediateField.fixedField H with hK
  have hmap : (p.map (algebraMap F K)).map (algebraMap K E) = p.map (algebraMap F E) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hroot : (p.map (algebraMap F K)).rootSet E = p.rootSet E := by
    simp only [Polynomial.rootSet, Polynomial.aroots, hmap]
  have hsplit : ((p.map (algebraMap F K)).map (algebraMap K E)).Splits := by
    rw [hmap]
    exact Polynomial.IsSplittingField.splits E p
  have hdeg' : (p.map (algebraMap F K)).natDegree ≠ 0 := by
    rwa [Polynomial.natDegree_map_eq_of_injective (algebraMap F K).injective]
  refine irreducible_of_transitive (E := E) (hsep.map) hsplit hdeg' ?_
  intro x hx y hy
  rw [hroot] at hx hy
  obtain ⟨σ, hσH, hσ⟩ := exists_mem_rootPerm_eq_of_ne_bot p hsurj hH ⟨x, hx⟩ ⟨y, hy⟩
  have hfix : σ ∈ IntermediateField.fixingSubgroup K :=
    (IntermediateField.mem_fixingSubgroup_iff K σ).mpr fun z hz =>
      (IntermediateField.mem_fixedField_iff H z).mp hz σ hσH
  exact ⟨IntermediateField.fixingSubgroupEquiv K ⟨σ, hfix⟩, hσ⟩

theorem splits_map_fixedField_bot [Polynomial.IsSplittingField F E p] :
    (p.map (algebraMap F
      (IntermediateField.fixedField (⊥ : Subgroup (E ≃ₐ[F] E))))).Splits := by
  rw [IntermediateField.fixedField_bot]
  have hcomp : ((IntermediateField.topEquiv (F := F) (E := E)).symm.toRingEquiv.toRingHom.comp
      (algebraMap F E)) = algebraMap F (⊤ : IntermediateField F E) :=
    RingHom.ext fun a => (IntermediateField.topEquiv (F := F) (E := E)).symm.commutes a
  have h := (Polynomial.IsSplittingField.splits E p).map
    (IntermediateField.topEquiv (F := F) (E := E)).symm.toRingEquiv.toRingHom
  rwa [Polynomial.map_map, hcomp] at h

theorem ne_bot_of_not_splits [Polynomial.IsSplittingField F E p] {H : Subgroup (E ≃ₐ[F] E)}
    (h : ¬ (p.map (algebraMap F (IntermediateField.fixedField H))).Splits) : H ≠ ⊥ := by
  rintro rfl
  exact h (splits_map_fixedField_bot p)

theorem irreducible_map_fixedField_of_not_splits [Polynomial.IsSplittingField F E p]
    (hsep : p.Separable) (hdeg : p.natDegree ≠ 0)
    (hsurj : Function.Surjective (rootPermHom (E := E) p))
    {H : Subgroup (E ≃ₐ[F] E)} [H.Normal]
    (h : ¬ (p.map (algebraMap F (IntermediateField.fixedField H))).Splits) :
    Irreducible (p.map (algebraMap F (IntermediateField.fixedField H))) :=
  irreducible_map_fixedField p hsep hdeg hsurj (ne_bot_of_not_splits p h)

end Rhone.Algebra.GaloisIrreducibility
