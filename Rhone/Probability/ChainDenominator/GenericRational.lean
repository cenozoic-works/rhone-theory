/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ChainDenominator.ScaledChain
public import Mathlib.FieldTheory.RatFunc.Degree

/-! # Generic chain degree at infinity, with rational-function reduction -/

@[expose] public section

noncomputable section

namespace Rhone.Probability.ChainDenominator

open Polynomial DiagonalChain

theorem W_generic_ne_zero (k : ℕ) (hk : 2 ≤ k) :
    W k (C (X : ℚ[X])) X ≠ 0 := by
  intro hz
  have h := W_map (mapRingHom (evalRingHom (1 : ℚ))) k (C (X : ℚ[X])) X
  simp only [coe_mapRingHom, map_C, coe_evalRingHom, eval_X, map_X] at h
  rw [hz, Polynomial.map_zero] at h
  exact W_poly_ne_zero (by norm_num : (0 : ℚ) < 1) hk h.symm

theorem frakE_generic_ne_zero (k : ℕ) :
    frakE k (C (X : ℚ[X])) X ≠ 0 := by
  intro hz
  have h := frakE_map (mapRingHom (evalRingHom (1 : ℚ))) k (C (X : ℚ[X])) X
  simp only [coe_mapRingHom, map_C, coe_evalRingHom, eval_X, map_X] at h
  rw [hz, Polynomial.map_zero] at h
  exact frakE_poly_ne_zero (by norm_num : (0 : ℚ) < 1) k h.symm

def genericNumerator (k : ℕ) : (RatFunc ℚ)[X] :=
  (W k (C (X : ℚ[X])) X).map (algebraMap ℚ[X] (RatFunc ℚ))

def genericDenominator (k : ℕ) : (RatFunc ℚ)[X] :=
  (frakE k (C (X : ℚ[X])) X).map (algebraMap ℚ[X] (RatFunc ℚ))

def genericQuotient (k : ℕ) : RatFunc (RatFunc ℚ) :=
  algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (genericNumerator k) /
    algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (genericDenominator k)

theorem genericNumerator_natDegree (k : ℕ) (hk : 1 ≤ k) :
    (genericNumerator k).natDegree = Nat.choose (k - 1) 2 := by
  rw [genericNumerator, natDegree_map_eq_of_injective (RatFunc.algebraMap_injective ℚ)]
  exact natDegree_W_generic k hk

theorem genericDenominator_natDegree (k : ℕ) :
    (genericDenominator k).natDegree = Nat.choose (k + 1) 2 - 1 := by
  rw [genericDenominator, natDegree_map_eq_of_injective (RatFunc.algebraMap_injective ℚ)]
  exact natDegree_frakE_generic k

theorem genericNumerator_ne_zero (k : ℕ) (hk : 2 ≤ k) : genericNumerator k ≠ 0 := by
  exact fun h => W_generic_ne_zero k hk
    ((Polynomial.map_injective _ (RatFunc.algebraMap_injective ℚ))
      (by simpa [genericNumerator] using h))

theorem genericDenominator_ne_zero (k : ℕ) : genericDenominator k ≠ 0 := by
  exact fun h => frakE_generic_ne_zero k
    ((Polynomial.map_injective _ (RatFunc.algebraMap_injective ℚ))
      (by simpa [genericDenominator] using h))

theorem genericQuotient_ne_zero (k : ℕ) (hk : 2 ≤ k) : genericQuotient k ≠ 0 := by
  exact div_ne_zero (RatFunc.algebraMap_ne_zero (genericNumerator_ne_zero k hk))
    (RatFunc.algebraMap_ne_zero (genericDenominator_ne_zero k))

theorem genericQuotient_intDegree (k : ℕ) (hk : 2 ≤ k) :
    (genericQuotient k).intDegree = 2 - 2 * (k : ℤ) := by
  rw [genericQuotient, RatFunc.intDegree_div
    (RatFunc.algebraMap_ne_zero (genericNumerator_ne_zero k hk))
    (RatFunc.algebraMap_ne_zero (genericDenominator_ne_zero k)),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial,
    genericNumerator_natDegree k (by omega), genericDenominator_natDegree]
  have h := degInfty_vartheta_zero (by norm_num : (0 : ℚ) < 1) hk
  rw [natDegree_W (by norm_num : (0 : ℚ) < 1) (by omega),
    natDegree_frakE (by norm_num : (0 : ℚ) < 1)] at h
  exact h

end Rhone.Probability.ChainDenominator
