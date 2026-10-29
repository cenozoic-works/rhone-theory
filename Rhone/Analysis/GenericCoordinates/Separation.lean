/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.GenericCoordinates.Coordinates

/-! # Squarefreeness and coprimality over `ℚ(θA,θB)` -/

@[expose] public section

namespace Rhone.Analysis.GenericCoordinates

open Polynomial LinearAlgebra.Tridiag

abbrev CanonicalField := FractionRing (MvPolynomial (Fin 2) ℚ)

noncomputable def canonicalThetaA : CanonicalField :=
  algebraMap (MvPolynomial (Fin 2) ℚ) CanonicalField (MvPolynomial.X 0)

noncomputable def canonicalThetaB : CanonicalField :=
  algebraMap (MvPolynomial (Fin 2) ℚ) CanonicalField (MvPolynomial.X 1)

noncomputable def canonicalToLaurent : CanonicalField →+*
    Rhone.Analysis.Rescale.LaurentK RatioField :=
  genericToLaurent.comp canonicalToGeneric

theorem canonicalToLaurent_injective : Function.Injective canonicalToLaurent :=
  canonicalToLaurent.injective

@[simp] theorem canonicalToLaurent_thetaA :
    canonicalToLaurent canonicalThetaA = Rhone.Analysis.Rescale.thetaA RatioField := by
  simp [canonicalToLaurent, canonicalThetaA, mutationCoordinates]

@[simp] theorem canonicalToLaurent_thetaB :
    canonicalToLaurent canonicalThetaB = Rhone.Analysis.Rescale.thetaB ratio := by
  simp [canonicalToLaurent, canonicalThetaB, mutationCoordinates]

theorem E_squarefree (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    Squarefree (E CanonicalField[X] i j (C canonicalThetaA) (C canonicalThetaB) X) := by
  let : CharZero RatioField := Rhone.Analysis.Rescale.charZero_qb
  exact Rhone.Analysis.Rescale.E_squarefree canonicalThetaA canonicalThetaB ratio
    canonicalToLaurent canonicalToLaurent_thetaA canonicalToLaurent_thetaB
    Rhone.Analysis.Rescale.qb_transcendental i j hi hj

theorem E_coprime (i j p q : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hne : (i, j) ≠ (p, q)) :
    IsCoprime (E CanonicalField[X] i j (C canonicalThetaA) (C canonicalThetaB) X)
      (E CanonicalField[X] p q (C canonicalThetaA) (C canonicalThetaB) X) := by
  let : CharZero RatioField := Rhone.Analysis.Rescale.charZero_qb
  exact Rhone.Analysis.Rescale.E_coprime_of_ne canonicalThetaA canonicalThetaB ratio
    canonicalToLaurent canonicalToLaurent_thetaA canonicalToLaurent_thetaB
    Rhone.Analysis.Rescale.qb_transcendental i j p q hi hj hp hq hne

end Rhone.Analysis.GenericCoordinates
