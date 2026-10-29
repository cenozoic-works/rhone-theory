/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.GenericCoordinates.Separation
public import Rhone.LinearAlgebra.SlotDeletion.Denom
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Generic denominator support outside a block's upper set -/

@[expose] public section

namespace Rhone.Probability.ResidueSupport
open Polynomial LinearAlgebra.SlotDeletion Analysis.GenericCoordinates

noncomputable def block (i j : ℕ) : Polynomial CanonicalField :=
  LinearAlgebra.Tridiag.E _ i j (C canonicalThetaA) (C canonicalThetaB) X

noncomputable def denominator (i j : ℕ) : Polynomial CanonicalField :=
  Dfull (C canonicalThetaA) (C canonicalThetaB) X i j

theorem mutation_shift_ne_zero (c : Fin 2) (n : ℕ) (hn : 0 < n) :
    algebraMap (MvPolynomial (Fin 2) ℚ) CanonicalField (MvPolynomial.X c) + n ≠ 0 := by
  intro h
  have hp : (MvPolynomial.X c + (n : MvPolynomial (Fin 2) ℚ)) = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) CanonicalField
    simpa using h
  have hq := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : ℚ))) hp
  have : (n : ℚ) = 0 := by simpa using hq
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) this

theorem poch_mutation_ne_zero (c : Fin 2) (n : ℕ) :
    poch (algebraMap (MvPolynomial (Fin 2) ℚ) CanonicalField (MvPolynomial.X c)) n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact mutation_shift_ne_zero c k (by have := (Finset.mem_Ico.mp hk).1; omega)

theorem block_coprime_denominator {p q i j : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hoff : ¬ (p ≤ i ∧ q ≤ j)) : IsCoprime (block p q) (denominator i j) := by
  have hA : IsUnit (poch (C canonicalThetaA) i : Polynomial CanonicalField) := by
    rw [← poch_map C]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (poch_mutation_ne_zero 0 i))
  have hB : IsUnit (poch (C canonicalThetaB) j : Polynomial CanonicalField) := by
    rw [← poch_map C]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (poch_mutation_ne_zero 1 j))
  unfold denominator Dfull
  apply IsCoprime.mul_right
  · obtain ⟨u, hu⟩ := hA.mul hB
    rw [← hu]
    exact ⟨0, ↑u⁻¹, by simp⟩
  · unfold Erect
    apply IsCoprime.prod_right
    intro a ha
    apply IsCoprime.prod_right
    intro b hb
    have ha' := Finset.mem_Ico.mp ha
    have hb' := Finset.mem_Ico.mp hb
    apply E_coprime p q a b (by omega) (by omega) (by omega) (by omega)
    intro heq
    have hpa := congrArg Prod.fst heq
    have hqb := congrArg Prod.snd heq
    simp only at hpa hqb
    apply hoff
    omega

theorem denominator_eval_ne_zero {L : Type*} [Field L]
    (φ : CanonicalField →+* L) (r : L) {p q i j : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hoff : ¬ (p ≤ i ∧ q ≤ j))
    (hroot : (block p q).eval₂ φ r = 0) :
    (denominator i j).eval₂ φ r ≠ 0 := by
  have h := (block_coprime_denominator hp hq hoff).map (Polynomial.eval₂RingHom φ r)
  exact h.ne_zero_or_ne_zero.resolve_left (by simpa using hroot)

theorem cleared_denom_eval_ne_zero {L : Type*} [Field L]
    (φ : CanonicalField →+* L) (r : L) {p q i j : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hoff : ¬ (p ≤ i ∧ q ≤ j))
    (hroot : (block p q).eval₂ φ r = 0) (N : Polynomial CanonicalField) :
    (RatFunc.denom (algebraMap _ (RatFunc CanonicalField) N /
      algebraMap _ (RatFunc CanonicalField) (denominator i j))).eval₂ φ r ≠ 0 := by
  intro hz
  exact denominator_eval_ne_zero φ r hp hq hoff hroot
    (Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero φ r (RatFunc.denom_div_dvd N _) hz)

theorem scaled_value_zero {L : Type*} [Field L] (r : L) (f : RatFunc L)
    (hregular : f.denom.eval r ≠ 0) :
    RatFunc.eval (RingHom.id L) r
      (algebraMap (Polynomial L) (RatFunc L) (X - C r) * f) = 0 := by
  have hx : (RatFunc.denom (algebraMap (Polynomial L) (RatFunc L) (X - C r))).eval₂
      (RingHom.id L) r ≠ 0 := by
    rw [RatFunc.denom_algebraMap]
    simp
  rw [RatFunc.eval_mul (RingHom.id L) r hx (by simpa using hregular)]
  rw [RatFunc.eval_algebraMap]
  simp

theorem cleared_scaled_value_zero {L : Type*} [Field L]
    (φ : CanonicalField →+* L) (r : L) {p q i j : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hoff : ¬ (p ≤ i ∧ q ≤ j))
    (hroot : (block p q).eval₂ φ r = 0) (N : Polynomial CanonicalField) :
    RatFunc.eval (RingHom.id L) r
      (algebraMap (Polynomial L) (RatFunc L) (X - C r) *
        (algebraMap _ (RatFunc L) (N.map φ) /
          algebraMap _ (RatFunc L) ((denominator i j).map φ))) = 0 := by
  apply scaled_value_zero
  intro hz
  have hd := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id L) r
    (RatFunc.denom_div_dvd (N.map φ) ((denominator i j).map φ)) (by simpa using hz)
  apply denominator_eval_ne_zero φ r hp hq hoff hroot
  simpa only [Polynomial.eval₂_id, Polynomial.eval_map] using hd

noncomputable def residueFamily {L : Type*} [Field L]
    (φ : CanonicalField →+* L) (r : L)
    (N : ℕ → ℕ → ℕ → Polynomial CanonicalField) (i j t : ℕ) : L :=
  RatFunc.eval (RingHom.id L) r
    (algebraMap (Polynomial L) (RatFunc L) (X - C r) *
      (algebraMap _ (RatFunc L) ((N i j t).map φ) /
        algebraMap _ (RatFunc L) ((denominator i j).map φ)))

theorem residueFamily_off {L : Type*} [Field L]
    (φ : CanonicalField →+* L) (r : L)
    (N : ℕ → ℕ → ℕ → Polynomial CanonicalField) {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hroot : (block p q).eval₂ φ r = 0) :
    ∀ i j t, ¬ (p ≤ i ∧ q ≤ j) → residueFamily φ r N i j t = 0 := by
  intro i j t hoff
  exact cleared_scaled_value_zero φ r hp hq hoff hroot (N i j t)

end Rhone.Probability.ResidueSupport
