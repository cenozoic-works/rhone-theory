/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ChainDenominator.MinorScaling

/-! # Generic principal-minor separation in the original mutation variable -/

@[expose] public section

noncomputable section

namespace Rhone.Probability.ChainDenominator

open Polynomial LinearAlgebra.Tridiag Analysis.DenominatorEquation LinearAlgebra.DenominatorEquation

variable {K : Type*} [Field K]

theorem exists_inverse_variable_hom : ∃ f : RatFunc K →+* RatFunc K,
    (∀ c : K, f (RatFunc.C c) = RatFunc.C c) ∧ f RatFunc.X = RatFunc.X⁻¹ := by
  have ht : Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
    simpa only [Transcendental, IsAlgebraic.inv_iff] using
      (RatFunc.transcendental_X : Transcendental K (RatFunc.X : RatFunc K))
  let φ : K[X] →+* RatFunc K := (aeval ((RatFunc.X : RatFunc K)⁻¹)).toRingHom
  have hinj : Function.Injective φ := transcendental_iff_injective.mp ht
  have hφ : nonZeroDivisors K[X] ≤ (nonZeroDivisors (RatFunc K)).comap φ := by
    intro p hp
    rw [Submonoid.mem_comap]
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    exact nonZeroDivisors.ne_zero hp (hinj (by simpa using h0))
  refine ⟨RatFunc.liftRingHom φ hφ, ?_, ?_⟩
  · intro c
    rw [RatFunc.liftRingHom_C]
    change (aeval ((RatFunc.X : RatFunc K)⁻¹)) (C c) = _
    rw [aeval_C]
    rfl
  · rw [RatFunc.liftRingHom_X]
    exact aeval_X _

variable [CharZero K]

theorem ordinaryMinors_isCoprime (i j cut : ℕ) (S : K) (hS : S ≠ 0) :
    IsCoprime
      (ordinaryMinor i j 0 cut (C (RatFunc.C S * RatFunc.X)) (X : (RatFunc K)[X]))
      (ordinaryMinor i j (cut + 1) (min i j - cut)
        (C (RatFunc.C S * RatFunc.X)) (X : (RatFunc K)[X])) := by
  obtain ⟨f, hfC, hfX⟩ := exists_inverse_variable_hom (K := K)
  have h := (ordinaryMinors_inverse_isCoprime i j cut S hS).map (mapRingHom f)
  simpa only [ordinaryMinor_map, coe_mapRingHom, map_C, map_X, map_div₀,
    hfC, hfX, div_inv_eq_mul] using h

theorem ordinaryMinor_leading {R : Type*} [CommRing R]
    (i j cut : ℕ) (θA θB ρ : R) :
    ordinaryMinor i j 0 cut (θA * (i : R) + θB * (j : R)) ρ =
      Delta R i j θA θB ρ cut := by
  unfold ordinaryMinor Delta
  simp only [Nat.zero_add, dcoefS_eq_dcoef]

theorem ordinaryMinor_trailing {R : Type*} [CommRing R]
    (i j cut : ℕ) (hcut : cut ≤ min i j) (θA θB ρ : R) :
    ordinaryMinor i j (cut + 1) (min i j - cut) (θA * (i : R) + θB * (j : R)) ρ =
      DeltaP R i j θA θB ρ (cut + 1) := by
  rw [DeltaP, LinearAlgebra.RecombinationExpansion.Qc_of_le _ _ _ (by omega)]
  rw [tridFrom_eq_trid_shift, det_trid_eq_cont]
  simp only [ordinaryMinor, dcoefS_eq_dcoef, Nat.add_sub_add_right, Nat.add_comm]

theorem Delta_DeltaP_generic_isCoprime (i j cut : ℕ) (hi : 1 ≤ i)
    (hcut : cut ≤ min i j) :
    IsCoprime
      (Delta (RatFunc K)[X] i j (C RatFunc.X) 0 X cut)
      (DeltaP (RatFunc K)[X] i j (C RatFunc.X) 0 X (cut + 1)) := by
  have h := ordinaryMinors_isCoprime i j cut (i : K) (Nat.cast_ne_zero.mpr (by omega))
  have hs : C (RatFunc.C (i : K) * RatFunc.X) =
      C (RatFunc.X : RatFunc K) * (i : (RatFunc K)[X]) + 0 * (j : (RatFunc K)[X]) := by
    simp only [map_mul, map_natCast, zero_mul, add_zero]
    ring
  rw [hs, ordinaryMinor_leading, ordinaryMinor_trailing i j cut hcut] at h
  exact h

theorem ratio_total_ne_zero (i j : ℕ) (hi : 1 ≤ i) :
    (i : RatFunc ℚ) + (j : RatFunc ℚ) * RatFunc.X ≠ 0 := by
  intro hz
  have hp : (C (i : ℚ) + C (j : ℚ) * X : ℚ[X]) = 0 := by
    apply RatFunc.algebraMap_injective ℚ
    simpa using hz
  have hc := congrArg (fun p : ℚ[X] => p.coeff 0) hp
  simp only [coeff_add, coeff_C_zero, coeff_mul_X_zero, add_zero, coeff_zero] at hc
  exact (Nat.cast_ne_zero.mpr (by omega : i ≠ 0)) hc

theorem Delta_DeltaP_ratio_isCoprime (i j cut : ℕ) (hi : 1 ≤ i)
    (hcut : cut ≤ min i j) :
    IsCoprime
      (Delta (RatFunc (RatFunc ℚ))[X] i j (C RatFunc.X)
        (C (RatFunc.C (RatFunc.X : RatFunc ℚ) * RatFunc.X)) X cut)
      (DeltaP (RatFunc (RatFunc ℚ))[X] i j (C RatFunc.X)
        (C (RatFunc.C (RatFunc.X : RatFunc ℚ) * RatFunc.X)) X (cut + 1)) := by
  have h := ordinaryMinors_isCoprime i j cut
    ((i : RatFunc ℚ) + (j : RatFunc ℚ) * RatFunc.X) (ratio_total_ne_zero i j hi)
  have hs : C (RatFunc.C ((i : RatFunc ℚ) + (j : RatFunc ℚ) * RatFunc.X) * RatFunc.X) =
      C (RatFunc.X : RatFunc (RatFunc ℚ)) * (i : (RatFunc (RatFunc ℚ))[X]) +
        C (RatFunc.C (RatFunc.X : RatFunc ℚ) * RatFunc.X) * (j : (RatFunc (RatFunc ℚ))[X]) := by
    simp only [map_add, map_mul, map_natCast]
    ring
  rw [hs, ordinaryMinor_leading, ordinaryMinor_trailing i j cut hcut] at h
  exact h

theorem Delta_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (i j cut : ℕ) (θA θB ρ : R) :
    f (Delta R i j θA θB ρ cut) = Delta T i j (f θA) (f θB) (f ρ) cut := by
  unfold Delta
  rw [Analysis.Rescale.cont_map]
  congr 1
  · funext t; simp [dcoef]
  · funext t; simp [bcoef, map_ofNat]
  · funext t; simp [ccoef]

theorem DeltaP_succ_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (i j cut : ℕ) (hcut : cut ≤ min i j) (θA θB ρ : R) :
    f (DeltaP R i j θA θB ρ (cut + 1)) =
      DeltaP T i j (f θA) (f θB) (f ρ) (cut + 1) := by
  rw [← ordinaryMinor_trailing i j cut hcut, ordinaryMinor_map]
  simp only [map_add, map_mul, map_natCast]
  exact ordinaryMinor_trailing i j cut hcut _ _ _

theorem DeltaP_ne_zero_of_Delta_eq_zero_ratio {F : Type*} [Field F]
    (f : RatFunc (RatFunc ℚ) →+* F) (i j : ℕ) (hi : 1 ≤ i) (ρ : F) :
    ∀ cut, cut < min i j →
      Delta F i j (f RatFunc.X) (f (RatFunc.C (RatFunc.X : RatFunc ℚ) * RatFunc.X)) ρ cut = 0 →
      DeltaP F i j (f RatFunc.X)
        (f (RatFunc.C (RatFunc.X : RatFunc ℚ) * RatFunc.X)) ρ (cut + 1) ≠ 0 := by
  intro cut hc hl hr
  have h := (Delta_DeltaP_ratio_isCoprime i j cut hi hc.le).map (eval₂RingHom f ρ)
  rw [Delta_map, DeltaP_succ_map _ i j cut hc.le] at h
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X] at h
  rw [hl, hr] at h
  exact not_isCoprime_zero_zero h

end Rhone.Probability.ChainDenominator
