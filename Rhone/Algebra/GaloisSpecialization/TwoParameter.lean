/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GaloisSpecialization.GenericSymmetricGalois
public import Rhone.Algebra.GaloisSpecialization.Transcendental
public import Rhone.Algebra.GaloisSpecialization.ParameterSum

/-! # Generic quintic and septic Galois groups with both mutation parameters -/

@[expose] public section

namespace Rhone.Algebra.GaloisSpecialization

open Polynomial LinearAlgebra.Tridiag

abbrev MutationField := RatFunc (RatFunc ℚ)

noncomputable def sumParameter : MutationField := algebraMap (RatFunc ℚ) MutationField RatFunc.X
noncomputable def differenceParameter : MutationField := RatFunc.X
noncomputable def thetaA : MutationField := (sumParameter + differenceParameter) / 2
noncomputable def thetaB : MutationField := (sumParameter - differenceParameter) / 2

theorem theta_sum : thetaA + thetaB = sumParameter := by
  unfold thetaA thetaB
  ring

theorem theta_difference : thetaA - thetaB = differenceParameter := by
  unfold thetaA thetaB
  ring

theorem diagonalFamily_two_parameter (m : ℕ) :
    ((diagonalFamily ℚ m).map (algebraMap ℚ[X] (RatFunc ℚ))).map
      (algebraMap (RatFunc ℚ) MutationField) =
    E MutationField[X] m m (C thetaA) (C thetaB) X := by
  rw [Polynomial.map_map]
  unfold diagonalFamily
  rw [← Polynomial.coe_mapRingHom,
    E_map (Polynomial.mapRingHom
      ((algebraMap (RatFunc ℚ) MutationField).comp (algebraMap ℚ[X] (RatFunc ℚ))))]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_zero,
    Polynomial.map_X, RingHom.comp_apply]
  rw [E_diagonal_polynomial_parameter_sum m thetaA thetaB, theta_sum]
  rfl

theorem E55gen_galois_full_two_var :
    Function.Bijective (Gal.galActionHom
      ((Rhone.Algebra.Galois.E55gen.map (algebraMap ℚ[X] (RatFunc ℚ))).map
        (algebraMap (RatFunc ℚ) MutationField))
      ((Rhone.Algebra.Galois.E55gen.map (algebraMap ℚ[X] (RatFunc ℚ))).map
        (algebraMap (RatFunc ℚ) MutationField)).SplittingField) :=
  galois_full_ratFunc_of_galois_full _
    Rhone.Algebra.Galois.E55gen_irreducible_ratFunc.separable
    Rhone.Algebra.GaloisDegreeSeven.E55gen_irreducible_two_var.separable E55gen_galois_full

theorem E77gen_galois_full_two_var :
    Function.Bijective (Gal.galActionHom
      ((Rhone.Algebra.GaloisDegreeSeven.E77gen.map (algebraMap ℚ[X] (RatFunc ℚ))).map
        (algebraMap (RatFunc ℚ) MutationField))
      ((Rhone.Algebra.GaloisDegreeSeven.E77gen.map (algebraMap ℚ[X] (RatFunc ℚ))).map
        (algebraMap (RatFunc ℚ) MutationField)).SplittingField) :=
  galois_full_ratFunc_of_galois_full _
    Rhone.Algebra.GaloisDegreeSeven.E77gen_irreducible_ratFunc.separable
    Rhone.Algebra.GaloisDegreeSeven.E77gen_irreducible_two_var.separable E77gen_galois_full

theorem E55_galois_full :
    Function.Bijective (Gal.galActionHom
      (E MutationField[X] 5 5 (C thetaA) (C thetaB) X)
      (E MutationField[X] 5 5 (C thetaA) (C thetaB) X).SplittingField) := by
  have h := diagonalFamily_two_parameter 5
  change ((Rhone.Algebra.Galois.E55gen.map (algebraMap ℚ[X] (RatFunc ℚ))).map
    (algebraMap (RatFunc ℚ) MutationField)) = _ at h
  exact Eq.mp (congrArg (fun r : MutationField[X] =>
    Function.Bijective (Gal.galActionHom r r.SplittingField)) h)
    E55gen_galois_full_two_var

theorem E77_galois_full :
    Function.Bijective (Gal.galActionHom
      (E MutationField[X] 7 7 (C thetaA) (C thetaB) X)
      (E MutationField[X] 7 7 (C thetaA) (C thetaB) X).SplittingField) := by
  have h := diagonalFamily_two_parameter 7
  change ((Rhone.Algebra.GaloisDegreeSeven.E77gen.map (algebraMap ℚ[X] (RatFunc ℚ))).map
    (algebraMap (RatFunc ℚ) MutationField)) = _ at h
  exact Eq.mp (congrArg (fun r : MutationField[X] =>
    Function.Bijective (Gal.galActionHom r r.SplittingField)) h)
    E77gen_galois_full_two_var

theorem card_rootSet_E55 :
    Fintype.card ((E MutationField[X] 5 5 (C thetaA) (C thetaB) X).rootSet
      (E MutationField[X] 5 5 (C thetaA) (C thetaB) X).SplittingField) = 5 := by
  have h := diagonalFamily_two_parameter 5
  change ((Rhone.Algebra.Galois.E55gen.map (algebraMap ℚ[X] (RatFunc ℚ))).map
    (algebraMap (RatFunc ℚ) MutationField)) = _ at h
  apply Eq.mp (congrArg (fun r : MutationField[X] =>
    Fintype.card (r.rootSet r.SplittingField) = 5) h)
  rw [card_rootSet_eq_natDegree
    Rhone.Algebra.GaloisDegreeSeven.E55gen_irreducible_two_var.separable
    (IsSplittingField.splits _ _), natDegree_map,
    natDegree_map_eq_of_injective (IsFractionRing.injective ℚ[X] (RatFunc ℚ)),
    Rhone.Algebra.Galois.E55gen_natDegree]

theorem card_rootSet_E77 :
    Fintype.card ((E MutationField[X] 7 7 (C thetaA) (C thetaB) X).rootSet
      (E MutationField[X] 7 7 (C thetaA) (C thetaB) X).SplittingField) = 7 := by
  have h := diagonalFamily_two_parameter 7
  change ((Rhone.Algebra.GaloisDegreeSeven.E77gen.map (algebraMap ℚ[X] (RatFunc ℚ))).map
    (algebraMap (RatFunc ℚ) MutationField)) = _ at h
  apply Eq.mp (congrArg (fun r : MutationField[X] =>
    Fintype.card (r.rootSet r.SplittingField) = 7) h)
  rw [card_rootSet_eq_natDegree
    Rhone.Algebra.GaloisDegreeSeven.E77gen_irreducible_two_var.separable
    (IsSplittingField.splits _ _), natDegree_map,
    natDegree_map_eq_of_injective (IsFractionRing.injective ℚ[X] (RatFunc ℚ)),
    Rhone.Algebra.GaloisDegreeSeven.natDegree_E77gen]

noncomputable def E55_galois_equiv_symmetric :
    (E MutationField[X] 5 5 (C thetaA) (C thetaB) X).Gal ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.ofBijective (Gal.galActionHom _ _) E55_galois_full).trans
    (Fintype.equivFinOfCardEq card_rootSet_E55).permCongrHom

noncomputable def E77_galois_equiv_symmetric :
    (E MutationField[X] 7 7 (C thetaA) (C thetaB) X).Gal ≃* Equiv.Perm (Fin 7) :=
  (MulEquiv.ofBijective (Gal.galActionHom _ _) E77_galois_full).trans
    (Fintype.equivFinOfCardEq card_rootSet_E77).permCongrHom

end Rhone.Algebra.GaloisSpecialization
