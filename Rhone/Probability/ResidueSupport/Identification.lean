/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ResidueSupport.Support
public import Rhone.Probability.SamplingUniform.ConstructionMap
public import Rhone.Probability.SamplingUniform.Generic

/-! # Identifying the coefficientwise cleared sampling hierarchy -/

@[expose] public section

namespace Rhone.Probability.ResidueSupport
open Polynomial LinearAlgebra.SlotDeletion SlotDeletion Analysis.GenericCoordinates
open SamplingUniform Analysis.RareAlleleHierarchy RareAlleleHierarchy

theorem denominator_ne_zero (i j : ℕ) : denominator i j ≠ 0 := by
  unfold denominator Dfull
  apply mul_ne_zero
  · apply mul_ne_zero
    · rw [← poch_map C]
      exact Polynomial.C_ne_zero.mpr (poch_mutation_ne_zero 0 i)
    · rw [← poch_map C]
      exact Polynomial.C_ne_zero.mpr (poch_mutation_ne_zero 1 j)
  · unfold Erect
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact (E_squarefree a b (by have := (Finset.mem_Ico.mp ha).1; omega)
      (by have := (Finset.mem_Ico.mp hb).1; omega)).ne_zero

noncomputable def toRational : Polynomial CanonicalField →+* RatFunc CanonicalField :=
  algebraMap _ _

theorem rational_Dfull_ne_zero (i j : ℕ) :
    Dfull (toRational (C canonicalThetaA)) (toRational (C canonicalThetaB))
      (toRational X) i j ≠ 0 := by
  rw [← Dfull_map]
  intro hz
  apply denominator_ne_zero i j
  apply RatFunc.algebraMap_injective CanonicalField
  change toRational (denominator i j) = toRational 0
  rw [map_zero]
  exact hz

noncomputable def frequencyNumerator (i j t : ℕ) :
    MvPolynomial (Fin 2) (Polynomial CanonicalField) :=
  clearedPhi (MvPolynomial.C (C canonicalThetaA)) (MvPolynomial.C (C canonicalThetaB))
    (MvPolynomial.C X) kapX gamX kapY gamY i j t

noncomputable def coefficientNumerator (m : Fin 2 →₀ ℕ) (i j t : ℕ) :
    Polynomial CanonicalField := (frequencyNumerator i j t).coeff m

theorem frequencyNumerator_map (i j t : ℕ) :
    MvPolynomial.map toRational (frequencyNumerator i j t) =
      clearedPhi (MvPolynomial.C (toRational (C canonicalThetaA)))
        (MvPolynomial.C (toRational (C canonicalThetaB))) (MvPolynomial.C (toRational X))
        kapX gamX kapY gamY i j t := by
  have hD : ∀ a b, Dfull (MvPolynomial.C (σ := Fin 2) (toRational (C canonicalThetaA)))
      (MvPolynomial.C (toRational (C canonicalThetaB)))
      (MvPolynomial.C (toRational X)) a b ≠ 0 := by
    intro a b
    rw [← Dfull_map]
    exact MvPolynomial.C_ne_zero.mpr (rational_Dfull_ne_zero a b)
  have h := clearedPhi_map (MvPolynomial.map toRational)
    (MvPolynomial.C (C canonicalThetaA)) (MvPolynomial.C (C canonicalThetaB))
    (MvPolynomial.C X) kapX gamX kapY gamY
    (by simpa using hD) i j t
  simpa [frequencyNumerator, kapX, gamX, kapY, gamY] using h

theorem genericPhi_coefficient (m : Fin 2 →₀ ℕ) (i j t : ℕ) :
    (genericPhi (toRational (C canonicalThetaA)) (toRational (C canonicalThetaB))
      (toRational X) i j t).coeff m =
      toRational (coefficientNumerator m i j t) / toRational (denominator i j) := by
  rw [genericPhi, MvPolynomial.coeff_C_mul, ← frequencyNumerator_map,
    MvPolynomial.coeff_map, ← Dfull_map]
  change (toRational (denominator i j))⁻¹ * toRational (coefficientNumerator m i j t) = _
  rw [div_eq_mul_inv, mul_comm]

theorem genericPhi_coefficient_regular {L : Type*} [Field L]
    (φ : CanonicalField →+* L) (r : L) (m : Fin 2 →₀ ℕ) {p q i j : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hoff : ¬ (p ≤ i ∧ q ≤ j))
    (hroot : (block p q).eval₂ φ r = 0) (t : ℕ) :
    (RatFunc.denom ((genericPhi (toRational (C canonicalThetaA))
      (toRational (C canonicalThetaB)) (toRational X) i j t).coeff m)).eval₂ φ r ≠ 0 := by
  rw [genericPhi_coefficient]
  exact cleared_denom_eval_ne_zero φ r hp hq hoff hroot (coefficientNumerator m i j t)

end Rhone.Probability.ResidueSupport
