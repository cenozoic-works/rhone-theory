/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationDegree.Unbounded

/-! # Exchange the spectral and recombination variables before localization -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open Polynomial MvPolynomial Algebra.DiagonalObstruction Analysis.DiagonalObstruction

variable (R : Type*) [CommSemiring R]

theorem coordinates_swap (P : Polynomial (Polynomial R)) :
    coordinates R (Polynomial.Bivariate.swap P) =
      rename (Equiv.swap (0 : Fin 2) 1) (coordinates R P) := by
  have h : (coordinates R).toAlgHom.comp Polynomial.Bivariate.swap.toAlgHom =
      (rename (Equiv.swap (0 : Fin 2) 1)).comp (coordinates R).toAlgHom := by
    ext <;> simp [Polynomial.Bivariate.swap_X, Polynomial.Bivariate.swap_Y]
  exact DFunLike.congr_fun h P

theorem swap_natDegree (P : Polynomial (Polynomial R)) :
    (Polynomial.Bivariate.swap P).natDegree = (coordinates R P).degreeOf 1 := by
  rw [← coordinates_spectral_degree, coordinates_swap]
  have h := degreeOf_rename_of_injective (Equiv.swap (0 : Fin 2) 1).injective
    (p := coordinates R P) (1 : Fin 2)
  simpa only [Equiv.swap_apply_right] using h

theorem swap_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (P : Polynomial (Polynomial R)) :
    Polynomial.Bivariate.swap (P.map (Polynomial.mapRingHom f)) =
      (Polynomial.Bivariate.swap P).map (Polynomial.mapRingHom f) := by
  have h : Polynomial.Bivariate.swap.toRingEquiv.toRingHom.comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom f)) =
      (Polynomial.mapRingHom (Polynomial.mapRingHom f)).comp
        Polynomial.Bivariate.swap.toRingEquiv.toRingHom := by
    ext a <;> simp [Polynomial.Bivariate.swap_C_C, Polynomial.Bivariate.swap_X,
      Polynomial.Bivariate.swap_Y]
  exact DFunLike.congr_fun h P

attribute [local instance] Polynomial.algebra

theorem integer_polynomial_algebraMap :
    algebraMap (Polynomial ℤ) (Polynomial ℚ) = Polynomial.mapRingHom (Int.castRingHom ℚ) := by
  ext <;> simp

theorem rational_swap_natDegree (F : Polynomial (Polynomial ℤ)) :
    (Polynomial.Bivariate.swap (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)))).natDegree =
      (coordinates ℤ F).degreeOf 1 := by
  rw [integer_polynomial_algebraMap, swap_map]
  rw [Polynomial.natDegree_map_eq_of_injective, swap_natDegree]
  exact Polynomial.map_injective _ Int.cast_injective

noncomputable def recombinationFactor (F : Polynomial (Polynomial ℤ)) :
    Polynomial (RatFunc ℚ) :=
  (Polynomial.Bivariate.swap (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)))).map
    (algebraMap (Polynomial ℚ) (RatFunc ℚ))

theorem recombinationFactor_natDegree (F : Polynomial (Polynomial ℤ)) :
    (recombinationFactor F).natDegree = (coordinates ℤ F).degreeOf 1 := by
  rw [recombinationFactor,
    Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _),
    rational_swap_natDegree]

theorem recombinationFactor_irreducible (F : Polynomial (Polynomial ℤ)) (hm : F.Monic)
    (hi : Irreducible (rationalFunctionFactor F)) (hd : 0 < (coordinates ℤ F).degreeOf 1) :
    Irreducible (recombinationFactor F) := by
  have hq : Irreducible (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) :=
    ((hm.map _).irreducible_iff_irreducible_map_fraction_map).mpr hi
  have hs : Irreducible
      (Polynomial.Bivariate.swap (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)))) :=
    (MulEquiv.irreducible_iff Polynomial.Bivariate.swap).mpr hq
  have hn : (Polynomial.Bivariate.swap
      (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)))).natDegree ≠ 0 := by
    rw [rational_swap_natDegree]
    omega
  exact ((hs.isPrimitive hn).irreducible_iff_irreducible_map_fraction_map).mp hs

theorem unbounded_irreducible_recombination_factor (D : ℕ) :
    ∃ m : ℕ, ∃ F : Polynomial (Polynomial ℤ),
      2 ≤ m ∧ F.Monic ∧ F ∣ spectralPolynomial m ∧ 0 ∈ factorLabels m F ∧
      Irreducible (recombinationFactor F) ∧
      recombinationFactor F ∣ recombinationFactor (spectralPolynomial m) ∧
      D < (recombinationFactor F).natDegree := by
  obtain ⟨m, F, hm, hmon, hdiv, hzero, hirr, hdeg⟩ :=
    unbounded_distinguished_recombination_degree D
  refine ⟨m, F, hm, hmon, hdiv, hzero,
    recombinationFactor_irreducible F hmon hirr (by omega), ?_, ?_⟩
  · exact Polynomial.map_dvd _ (map_dvd Polynomial.Bivariate.swap.toRingHom
      (Polynomial.map_dvd _ hdiv))
  · rwa [recombinationFactor_natDegree]

end Rhone.Probability.RecombinationDegree
