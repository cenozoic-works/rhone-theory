/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ChainDenominator.GenericResidue
public import Rhone.Algebra.Sharpness.Specialization

/-! # Disjoint level sets give coprime factors in the zero-scaling fibre of the minors -/

@[expose] public section

noncomputable section

namespace Rhone.Probability.ChainDenominator

open Polynomial LinearAlgebra.Tridiag

variable {K : Type*} [Field K] [CharZero K]

theorem affine_level_isCoprime (S : K) (hS : S ≠ 0) (t u : ℕ) (htu : t ≠ u) :
    IsCoprime (C S + C (t : K) * X) (C S + C (u : K) * X) := by
  have htu' : (u : K) - (t : K) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast htu.symm)
  have hd : S * ((u : K) - (t : K)) ≠ 0 := mul_ne_zero hS htu'
  let d := S * ((u : K) - (t : K))
  refine ⟨C ((u : K) / d), C (-(t : K) / d), ?_⟩
  have hlin : C (u : K) * (C S + C (t : K) * X) -
      C (t : K) * (C S + C (u : K) * X) = C d := by
    simp only [d, map_mul, map_sub]
    ring
  calc
    _ = C d⁻¹ * (C (u : K) * (C S + C (t : K) * X) -
        C (t : K) * (C S + C (u : K) * X)) := by
      simp only [div_eq_mul_inv, map_mul, map_neg]
      ring
    _ = 1 := by rw [hlin, ← map_mul, inv_mul_cancel₀ hd, map_one]

theorem level_products_isCoprime (S : K) (hS : S ≠ 0) (a b : Finset ℕ)
    (hab : Disjoint a b) :
    IsCoprime (∏ t ∈ a, (C S + C (t : K) * X))
      (∏ u ∈ b, (C S + C (u : K) * X)) := by
  apply IsCoprime.prod_left
  intro t ht
  apply IsCoprime.prod_right
  intro u hu
  apply affine_level_isCoprime S hS t u
  intro heq
  subst u
  exact Finset.disjoint_left.mp hab ht hu

def rescaledMinor {R : Type*} [CommRing R] (i j offset len : ℕ) (S σ : R) : R[X] :=
  cont (fun t => C S + C ((offset + t : ℕ) : R) * X +
      C (σ * Analysis.Rescale.ncoef R i j (offset + t)))
    (fun t => C (σ * bcoef R i j (offset + t)))
    (fun t => ccoef R[X] X (offset + t)) len

theorem rescaledMinor_zero {R : Type*} [CommRing R]
    (i j offset len : ℕ) (S : R) :
    rescaledMinor i j offset len S 0 =
      ∏ t ∈ Finset.range len, (C S + C ((offset + t : ℕ) : R) * X) := by
  unfold rescaledMinor
  simp only [zero_mul, map_zero, add_zero]
  exact Analysis.Rescale.cont_of_b_zero _ _ _

theorem rescaledMinor_map {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (i j offset len : ℕ) (S σ : R) :
    (rescaledMinor i j offset len S σ).map f =
      rescaledMinor i j offset len (f S) (f σ) := by
  unfold rescaledMinor
  rw [← coe_mapRingHom, Analysis.Rescale.cont_map]
  congr 1
  · funext t
    simp [Analysis.Rescale.ncoef]
  · funext t
    simp [bcoef, map_ofNat]
  · funext t
    simp [ccoef]

theorem rescaledMinors_zero_isCoprime (i j cut : ℕ)
    (S : K) (hS : S ≠ 0) :
    IsCoprime (rescaledMinor i j 0 cut S 0)
      (rescaledMinor i j (cut + 1) (min i j - cut) S 0) := by
  rw [rescaledMinor_zero, rescaledMinor_zero]
  apply IsCoprime.prod_left
  intro t ht
  apply IsCoprime.prod_right
  intro u hu
  apply affine_level_isCoprime S hS
  rw [Finset.mem_range] at ht hu
  omega

theorem cont_degree_le_size {R : Type*} [CommRing R] (d b c : ℕ → R[X])
    (hd : ∀ t, (d t).natDegree ≤ 1) (hbc : ∀ t, (b t * c t).natDegree ≤ 1) :
    ∀ n, (cont d b c n).natDegree ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [cont]
    | 1 => simpa [cont] using hd 0
    | n + 2 =>
      rw [cont]
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · have hm := natDegree_mul_le (p := d (n + 1)) (q := cont d b c (n + 1))
        have hh := hd (n + 1)
        have hi := ih (n + 1) (by omega)
        omega
      · have hm := natDegree_mul_le (p := b n * c n) (q := cont d b c n)
        have hh := hbc n
        have hi := ih n (by omega)
        omega

theorem rescaledMinor_degree_le {R : Type*} [CommRing R]
    (i j offset len : ℕ) (S σ : R) :
    (rescaledMinor i j offset len S σ).natDegree ≤ len := by
  apply cont_degree_le_size
  · intro t
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · rw [natDegree_C]; omega
      · apply natDegree_mul_le.trans
        rw [natDegree_C, Nat.zero_add]
        exact natDegree_X_le
    · rw [natDegree_C]; omega
  · intro t
    apply natDegree_mul_le.trans
    simp only [natDegree_C, Nat.zero_add, ccoef, natDegree_neg]
    apply natDegree_mul_le.trans
    have hc : (((offset + t : ℕ) : R[X]) + 1).natDegree = 0 := by
      rw [← Nat.cast_add_one]
      exact natDegree_natCast _
    rw [hc]
    exact natDegree_X_le

theorem rescaledMinor_zero_degree (i j offset len : ℕ) (ho : 1 ≤ offset) (S : K) :
    (rescaledMinor i j offset len S 0).natDegree = len := by
  rw [rescaledMinor_zero]
  have hf (t : ℕ) : (C S + C ((offset + t : ℕ) : K) * X).natDegree = 1 := by
    rw [add_comm, natDegree_add_C, natDegree_C_mul_X]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hn (t : ℕ) : C S + C ((offset + t : ℕ) : K) * X ≠ 0 := by
    intro h
    have hh := hf t
    rw [h, natDegree_zero] at hh
    omega
  rw [natDegree_prod _ _ (fun t _ => hn t)]
  simp only [hf, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

theorem rescaledMinor_zero_ne_zero (i j offset len : ℕ) (ho : 1 ≤ offset) (S : K) :
    rescaledMinor i j offset len S 0 ≠ 0 := by
  rw [rescaledMinor_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro t _ ht
  have hc := congrArg (fun p : K[X] => p.coeff 1) ht
  simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X_one, mul_one, coeff_zero,
    show (1 : ℕ) ≠ 0 from by omega, ite_false, zero_add] at hc
  exact (Nat.cast_ne_zero.mpr (by omega : offset + t ≠ 0)) hc

def genericMinor (i j offset len : ℕ) (S : K) : (RatFunc K)[X] :=
  (rescaledMinor i j offset len (C S) X).map (algebraMap K[X] (RatFunc K))

theorem genericMinors_isCoprime (i j cut : ℕ) (S : K) (hS : S ≠ 0) :
    IsCoprime (genericMinor i j 0 cut S)
      (genericMinor i j (cut + 1) (min i j - cut) S) := by
  let f := rescaledMinor i j 0 cut (C S) (X : K[X])
  let g := rescaledMinor i j (cut + 1) (min i j - cut) (C S) (X : K[X])
  let s := evalRingHom (0 : K)
  have hf : f.map s = rescaledMinor i j 0 cut S 0 := by
    simp [f, s, rescaledMinor_map]
  have hg : g.map s = rescaledMinor i j (cut + 1) (min i j - cut) S 0 := by
    simp [g, s, rescaledMinor_map]
  have hdeg : (g.map s).natDegree = g.natDegree := by
    have hu := rescaledMinor_degree_le i j (cut + 1) (min i j - cut) (C S) (X : K[X])
    have hl := natDegree_map_le (p := g) (f := s)
    rw [hg, rescaledMinor_zero_degree i j (cut + 1) _ (by omega) S] at hl ⊢
    exact le_antisymm hl hu
  have hne : g.map s ≠ 0 := by
    rw [hg]
    exact rescaledMinor_zero_ne_zero i j (cut + 1) _ (by omega) S
  have hlead : s g.leadingCoeff ≠ 0 := by
    have h := leadingCoeff_ne_zero.mpr hne
    simpa only [leadingCoeff, hdeg, coeff_map] using h
  apply IsCoprime.symm
  apply Algebra.Sharpness.isCoprime_map_of_specialization_one_leadingCoeff
    (algebraMap K[X] (RatFunc K)) s (RatFunc.algebraMap_injective K) g f hlead
  rw [hf, hg]
  exact (rescaledMinors_zero_isCoprime i j cut S hS).symm

end Rhone.Probability.ChainDenominator
