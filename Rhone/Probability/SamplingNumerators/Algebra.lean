/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Numerator
public import Rhone.Algebra.DiagonalIrreducibility.GenericRho
public import Rhone.Probability.Sharpness.PoleTransfer
public import Mathlib.RingTheory.Polynomial.Basic

/-! # Prime denominator transfer for the explicit sampling polynomials -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators
open Polynomial

theorem prime_dvd_clearing
    {R F : Type*} [CommRing R] [Field F]
    (ι : R →+* F) (hι : Function.Injective ι)
    {N D E d n : R} {v : F}
    (hE : Prime E) (hED : E ∣ D) (hEN : ¬ E ∣ N)
    (hN : ι N = ι D * v) (hd : ι d * v = ι n) : E ∣ d := by
  have heq : d * N = D * n := by
    apply hι
    simp only [map_mul]
    rw [hN]
    calc ι d * (ι D * v) = ι D * (ι d * v) := by ring
         _ = ι D * ι n := by rw [hd]
  have h : E ∣ d * N := heq ▸ hED.mul_right n
  exact (hE.dvd_mul.mp h).resolve_right hEN

theorem constant_prime_not_dvd_of_coeff
    {R : Type*} [CommRing R] {E : R} {N : Polynomial R} (k : ℕ)
    (hE : ¬ IsUnit E) (hc : IsCoprime (N.coeff k) E) : ¬ C E ∣ N := by
  intro h
  have hd := (C_dvd_iff_dvd_coeff E N).mp h k
  exact hE (isUnit_of_dvd_one (hc.symm.dvd_of_dvd_mul_left (by simpa using hd)))

theorem not_dvd_unit_mul_add
    {R : Type*} [CommRing R] {E N u L : R}
    (hu : IsUnit u) (hN : ¬ E ∣ N) : ¬ E ∣ u * N + E * L := by
  intro h
  have hd : E ∣ u * N := by
    have := dvd_sub h (dvd_mul_right E L)
    simpa using this
  obtain ⟨v, hv⟩ := isUnit_iff_dvd_one.mp hu
  apply hN
  apply hd.trans
  refine ⟨v, ?_⟩
  calc N = 1 * N := by ring
       _ = (u * v) * N := by rw [← hv]
       _ = (u * N) * v := by ring

end Rhone.Probability.SamplingNumerators
