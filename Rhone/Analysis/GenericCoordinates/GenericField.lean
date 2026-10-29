/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.Rescale.Discharge

/-! # Generic rational coordinates for block separation -/

@[expose] public section

namespace Rhone.Analysis.GenericCoordinates

open Polynomial
open LinearAlgebra.Tridiag

abbrev RatioField := FractionRing (Polynomial ℚ)
abbrev GenericField := FractionRing (Polynomial RatioField)

noncomputable def ratio : RatioField := Rhone.Analysis.Rescale.qb

noncomputable def sigmaVariable : GenericField :=
  algebraMap (Polynomial RatioField) GenericField X

noncomputable def ratioIn : GenericField :=
  algebraMap (Polynomial RatioField) GenericField (C ratio)

noncomputable def thetaA : GenericField := sigmaVariable⁻¹
noncomputable def thetaB : GenericField := ratioIn * sigmaVariable⁻¹

noncomputable def polynomialToLaurent : Polynomial RatioField →+*
    Rhone.Analysis.Rescale.LaurentK RatioField :=
  (algebraMap (PowerSeries RatioField) (Rhone.Analysis.Rescale.LaurentK RatioField)).comp
    Polynomial.coeToPowerSeries.ringHom

theorem polynomialToLaurent_injective : Function.Injective polynomialToLaurent :=
  (IsFractionRing.injective (PowerSeries RatioField)
    (Rhone.Analysis.Rescale.LaurentK RatioField)).comp (Polynomial.coe_injective RatioField)

noncomputable def genericToLaurent : GenericField →+*
    Rhone.Analysis.Rescale.LaurentK RatioField :=
  IsFractionRing.lift polynomialToLaurent_injective

theorem genericToLaurent_injective : Function.Injective genericToLaurent :=
  genericToLaurent.injective

@[simp] theorem genericToLaurent_variable :
    genericToLaurent sigmaVariable = Rhone.Analysis.Rescale.sig RatioField := by
  change IsFractionRing.lift polynomialToLaurent_injective
    (algebraMap (Polynomial RatioField) GenericField X) = _
  rw [IsFractionRing.lift_algebraMap]
  simp [polynomialToLaurent, Rhone.Analysis.Rescale.sig]

@[simp] theorem genericToLaurent_ratioIn :
    genericToLaurent ratioIn = Rhone.Analysis.Rescale.kToL RatioField ratio := by
  change IsFractionRing.lift polynomialToLaurent_injective
    (algebraMap (Polynomial RatioField) GenericField (C ratio)) = _
  rw [IsFractionRing.lift_algebraMap]
  simp [polynomialToLaurent, Rhone.Analysis.Rescale.kToL]

@[simp] theorem genericToLaurent_thetaA :
    genericToLaurent thetaA = Rhone.Analysis.Rescale.thetaA RatioField := by
  simp [thetaA, Rhone.Analysis.Rescale.thetaA]

@[simp] theorem genericToLaurent_thetaB :
    genericToLaurent thetaB = Rhone.Analysis.Rescale.thetaB ratio := by
  simp [thetaB, Rhone.Analysis.Rescale.thetaB]

theorem variable_ne_zero : sigmaVariable ≠ 0 := by
  intro h
  apply (X_ne_zero : (X : Polynomial RatioField) ≠ 0)
  apply IsFractionRing.injective (Polynomial RatioField) GenericField
  rw [map_zero]
  exact h

theorem variable_eq_thetaA_inv : sigmaVariable = thetaA⁻¹ := by
  simp [thetaA]

theorem ratioIn_eq_thetaB_div_thetaA : ratioIn = thetaB / thetaA := by
  rw [thetaB, thetaA]
  exact (mul_div_cancel_right₀ ratioIn (inv_ne_zero variable_ne_zero)).symm

theorem E_squarefree_generic (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    Squarefree (E GenericField[X] i j (C thetaA) (C thetaB) X) := by
  let : CharZero RatioField := Rhone.Analysis.Rescale.charZero_qb
  exact Rhone.Analysis.Rescale.E_squarefree thetaA thetaB ratio genericToLaurent
    genericToLaurent_thetaA genericToLaurent_thetaB
    Rhone.Analysis.Rescale.qb_transcendental i j hi hj

theorem E_coprime_generic (i j p q : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hne : (i, j) ≠ (p, q)) :
    IsCoprime (E GenericField[X] i j (C thetaA) (C thetaB) X)
      (E GenericField[X] p q (C thetaA) (C thetaB) X) := by
  let : CharZero RatioField := Rhone.Analysis.Rescale.charZero_qb
  exact Rhone.Analysis.Rescale.E_coprime_of_ne thetaA thetaB ratio genericToLaurent
    genericToLaurent_thetaA genericToLaurent_thetaB
    Rhone.Analysis.Rescale.qb_transcendental i j p q hi hj hp hq hne

end Rhone.Analysis.GenericCoordinates
