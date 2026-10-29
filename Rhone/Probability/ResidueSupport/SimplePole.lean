/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ResidueSupport.Identification
public import Mathlib.FieldTheory.Perfect

/-! # Simple poles of the explicit generic clearing denominators -/

@[expose] public section

namespace Rhone.Probability.ResidueSupport
open Polynomial LinearAlgebra.SlotDeletion SlotDeletion Analysis.GenericCoordinates

theorem block_separable {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    (block i j).Separable :=
  PerfectField.separable_iff_squarefree.mpr (E_squarefree i j hi hj)

theorem denominator_separable (i j : ℕ) : (denominator i j).Separable := by
  have hA : IsUnit (poch (C canonicalThetaA) i : Polynomial CanonicalField) := by
    rw [← poch_map C]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (poch_mutation_ne_zero 0 i))
  have hB : IsUnit (poch (C canonicalThetaB) j : Polynomial CanonicalField) := by
    rw [← poch_map C]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (poch_mutation_ne_zero 1 j))
  unfold denominator Dfull
  apply Separable.unit_mul (hA.mul hB)
  unfold Erect
  apply separable_prod'
  · intro a ha b hb hab
    apply IsCoprime.prod_left
    intro c hc
    apply IsCoprime.prod_right
    intro d hd
    apply E_coprime a c b d
      (by have := (Finset.mem_Ico.mp ha).1; omega)
      (by have := (Finset.mem_Ico.mp hc).1; omega)
      (by have := (Finset.mem_Ico.mp hb).1; omega)
      (by have := (Finset.mem_Ico.mp hd).1; omega)
    exact fun he => hab (congrArg Prod.fst he)
  · intro a ha
    apply separable_prod'
    · intro b hb c hc hbc
      apply E_coprime a b a c
        (by have := (Finset.mem_Ico.mp ha).1; omega)
        (by have := (Finset.mem_Ico.mp hb).1; omega)
        (by have := (Finset.mem_Ico.mp ha).1; omega)
        (by have := (Finset.mem_Ico.mp hc).1; omega)
      exact fun he => hbc (congrArg Prod.snd he)
    · intro b hb
      exact block_separable (by have := (Finset.mem_Ico.mp ha).1; omega)
        (by have := (Finset.mem_Ico.mp hb).1; omega)

theorem regular_mul_at {K : Type*} [Field K] (r : K) {f g : RatFunc K}
    (hf : f.denom.eval r ≠ 0) (hg : g.denom.eval r ≠ 0) :
    (f * g).denom.eval r ≠ 0 := by
  intro hz
  have h := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id K) r
    (RatFunc.denom_mul_dvd f g) hz
  exact (mul_ne_zero hf hg) (by simpa using h)

theorem scaled_fraction_regular {K : Type*} [Field K] (r : K) (N D : Polynomial K)
    (hD : D.Separable) :
    (RatFunc.denom (algebraMap (Polynomial K) (RatFunc K) (X - C r) *
      (algebraMap _ (RatFunc K) N / algebraMap _ (RatFunc K) D))).eval r ≠ 0 := by
  by_cases hz : D.eval r = 0
  · obtain ⟨Q, hQ⟩ := (Polynomial.dvd_iff_isRoot).mpr hz
    have hQeval : Q.eval r ≠ 0 := by
      have hd := hD.eval₂_derivative_ne_zero (RingHom.id K) hz
      rw [hQ] at hd
      simpa [Polynomial.derivative_mul] using hd
    have hx : algebraMap (Polynomial K) (RatFunc K) (X - C r) ≠ 0 := by
      exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero r)
    have heq : algebraMap (Polynomial K) (RatFunc K) (X - C r) *
        (algebraMap _ (RatFunc K) N / algebraMap _ (RatFunc K) D) =
        algebraMap _ (RatFunc K) N / algebraMap _ (RatFunc K) Q := by
      rw [hQ, map_mul, ← mul_div_assoc]
      exact mul_div_mul_left _ _ hx
    rw [heq]
    intro hzero
    exact hQeval (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id K) r
      (RatFunc.denom_div_dvd N Q) hzero)
  · apply regular_mul_at r
    · rw [RatFunc.denom_algebraMap]
      simp
    · intro hzero
      exact hz (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id K) r
        (RatFunc.denom_div_dvd N D) hzero)

theorem cleared_scaled_regular {L : Type*} [Field L] (φ : CanonicalField →+* L)
    (r : L) (N : Polynomial CanonicalField) (i j : ℕ) :
    (RatFunc.denom (algebraMap (Polynomial L) (RatFunc L) (X - C r) *
      (algebraMap _ (RatFunc L) (N.map φ) /
        algebraMap _ (RatFunc L) ((denominator i j).map φ)))).eval r ≠ 0 :=
  scaled_fraction_regular r _ _ (denominator_separable i j).map

end Rhone.Probability.ResidueSupport
