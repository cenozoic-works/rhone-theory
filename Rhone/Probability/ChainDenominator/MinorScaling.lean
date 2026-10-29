/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ChainDenominator.MinorFiber

/-! # Transport of principal-window coprimality out of the rescaled coordinates -/

@[expose] public section

noncomputable section

namespace Rhone.Probability.ChainDenominator

open Polynomial LinearAlgebra.Tridiag Analysis.DenominatorEquation LinearAlgebra.DenominatorEquation

theorem cont_scale {R : Type*} [CommRing R] (σ : R) (d b c : ℕ → R) :
    ∀ n, cont (fun t => σ * d t) (fun t => σ * b t) (fun t => σ * c t) n =
      σ ^ n * cont d b c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [cont]
    | 1 => simp [cont]
    | n + 2 =>
      rw [cont, cont, ih (n + 1) (by omega), ih n (by omega)]
      ring

def ordinaryMinor {R : Type*} [CommRing R] (i j offset len : ℕ) (s ρ : R) : R :=
  cont (fun t => dcoefS R i j s ρ (offset + t))
    (fun t => bcoef R i j (offset + t)) (fun t => ccoef R ρ (offset + t)) len

theorem rescaledMinor_eval {R : Type*} [CommRing R]
    (i j offset len : ℕ) (S σ z : R) :
    (rescaledMinor i j offset len S σ).eval z =
      cont (fun t => S + ((offset + t : ℕ) : R) * z +
        σ * Analysis.Rescale.ncoef R i j (offset + t))
        (fun t => σ * bcoef R i j (offset + t))
        (fun t => ccoef R z (offset + t)) len := by
  unfold rescaledMinor
  rw [← coe_evalRingHom, Analysis.Rescale.cont_map]
  congr 1
  · funext t; simp
  · funext t; simp
  · funext t; simp [ccoef]

theorem rescaledMinor_eval_eq {R : Type*} [CommRing R]
    (i j offset len : ℕ) (s ρ S σ z : R) (hs : σ * s = S) (hz : σ * ρ = z) :
    (rescaledMinor i j offset len S σ).eval z =
      σ ^ len * ordinaryMinor i j offset len s ρ := by
  rw [rescaledMinor_eval, ordinaryMinor, ← cont_scale]
  congr 1
  · funext t
    rw [dcoefS, Analysis.Rescale.ncoef, ← hs, ← hz]
    ring
  · funext t
    rw [ccoef, ccoef, ← hz]
    ring

theorem ordinaryMinor_map {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (i j offset len : ℕ) (s ρ : R) :
    f (ordinaryMinor i j offset len s ρ) =
      ordinaryMinor i j offset len (f s) (f ρ) := by
  unfold ordinaryMinor
  rw [Analysis.Rescale.cont_map]
  congr 1
  · funext t; simp [dcoefS]
  · funext t; simp [bcoef, map_ofNat]
  · funext t; simp [ccoef]

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem genericMinor_eq (i j offset len : ℕ) (S : K) :
    genericMinor i j offset len S =
      rescaledMinor i j offset len (RatFunc.C S) (RatFunc.X : RatFunc K) := by
  rw [genericMinor, rescaledMinor_map, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

theorem ordinaryMinors_inverse_isCoprime (i j cut : ℕ) (S : K) (hS : S ≠ 0) :
    IsCoprime
      (ordinaryMinor i j 0 cut (C (RatFunc.C S / RatFunc.X)) (X : (RatFunc K)[X]))
      (ordinaryMinor i j (cut + 1) (min i j - cut)
        (C (RatFunc.C S / RatFunc.X)) (X : (RatFunc K)[X])) := by
  have h := (genericMinors_isCoprime i j cut S hS).map
    (eval₂RingHom (C : RatFunc K →+* (RatFunc K)[X]) (C RatFunc.X * X))
  have he (offset len : ℕ) :
      (eval₂RingHom (C : RatFunc K →+* (RatFunc K)[X]) (C RatFunc.X * X))
        (genericMinor i j offset len S) =
      (C (RatFunc.X : RatFunc K)) ^ len *
        ordinaryMinor i j offset len (C (RatFunc.C S / RatFunc.X)) X := by
    rw [genericMinor_eq, coe_eval₂RingHom, ← eval_map, rescaledMinor_map]
    apply rescaledMinor_eval_eq
    · rw [← map_mul, mul_div_cancel₀ _ RatFunc.X_ne_zero]
    · rfl
  rw [he, he] at h
  exact h.of_mul_left_right.of_mul_right_right

end Rhone.Probability.ChainDenominator
