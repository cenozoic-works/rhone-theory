/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationDegree.FactorDegree
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # Outer spectral variable is coordinate 0; inner recombination variable is coordinate 1 -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open Polynomial MvPolynomial

variable (R : Type*) [CommSemiring R]

noncomputable def oneVariable : Polynomial R ≃ₐ[R] MvPolynomial (Fin 1) R :=
  (uniqueAlgEquiv R (Fin 1)).symm

noncomputable def coordinates : Polynomial (Polynomial R) ≃ₐ[R] MvPolynomial (Fin 2) R :=
  (Polynomial.mapAlgEquiv (oneVariable R)).trans (finSuccEquiv R 1).symm

@[simp] theorem oneVariable_C (a : R) : oneVariable R (Polynomial.C a) = MvPolynomial.C a := by
  apply (uniqueAlgEquiv R (Fin 1)).injective
  simp [oneVariable, uniqueAlgEquiv]

@[simp] theorem oneVariable_X : oneVariable R Polynomial.X = MvPolynomial.X 0 := by
  apply (uniqueAlgEquiv R (Fin 1)).injective
  simp [oneVariable, uniqueAlgEquiv]

@[simp] theorem finSucc_coordinates (P : Polynomial (Polynomial R)) :
    finSuccEquiv R 1 (coordinates R P) = P.map (oneVariable R).toRingHom := by
  simp [coordinates, Polynomial.mapAlgEquiv]

@[simp] theorem coordinates_C_C (a : R) :
    coordinates R (Polynomial.C (Polynomial.C a)) = MvPolynomial.C a := by
  apply (finSuccEquiv R 1).injective
  rw [finSucc_coordinates]
  simp [finSuccEquiv_apply]

@[simp] theorem coordinates_X : coordinates R Polynomial.X = MvPolynomial.X 0 := by
  apply (finSuccEquiv R 1).injective
  rw [finSucc_coordinates]
  simp [finSuccEquiv_apply]

@[simp] theorem coordinates_C_X :
    coordinates R (Polynomial.C Polynomial.X) = MvPolynomial.X 1 := by
  apply (finSuccEquiv R 1).injective
  rw [finSucc_coordinates]
  change Polynomial.map _ (Polynomial.C Polynomial.X) =
    finSuccEquiv R 1 (MvPolynomial.X (0 : Fin 1).succ)
  rw [finSuccEquiv_X_succ]
  simp

theorem coordinates_spectral_degree (P : Polynomial (Polynomial R)) :
    (coordinates R P).degreeOf 0 = P.natDegree := by
  rw [← natDegree_finSuccEquiv, finSucc_coordinates]
  exact Polynomial.natDegree_map_eq_of_injective (oneVariable R).injective P

theorem coordinates_coefficient_degree_le (P : Polynomial (Polynomial R)) (k : ℕ) :
    (P.coeff k).natDegree ≤ (coordinates R P).degreeOf 1 := by
  classical
  by_cases h : P.coeff k = 0
  · simp [h]
  have hn : (oneVariable R (P.coeff k)).coeff
      (Finsupp.single 0 (P.coeff k).natDegree) ≠ 0 := by
    change ((uniqueAlgEquiv R (Fin 1)).symm (P.coeff k)).coeff _ ≠ 0
    rw [coeff_uniqueAlgEquiv_symm]
    simpa only [Fin.default_eq_zero, Finsupp.single_eq_same, Polynomial.coeff_natDegree]
      using (Polynomial.leadingCoeff_ne_zero.mpr h)
  have hl := monomial_le_degreeOf 0 (MvPolynomial.mem_support_iff.mpr hn)
  have hr := degreeOf_coeff_finSuccEquiv (coordinates R P) (0 : Fin 1) k
  rw [finSucc_coordinates, Polynomial.coeff_map] at hr
  exact le_trans (by simpa using hl) hr

end Rhone.Probability.RecombinationDegree
