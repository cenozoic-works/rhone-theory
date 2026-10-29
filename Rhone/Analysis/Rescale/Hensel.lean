/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.Rescale.Rescale
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Polynomial.Identities

/-! # Hensel lift of the `σ = 0` roots of the rescaled determinant, with its linear term -/

@[expose] public section

namespace Rhone.Analysis.Rescale

open Polynomial LinearAlgebra.Tridiag DenominatorEquation

section Coeff

variable {R : Type*} [CommRing R]

theorem coeff_one_mul (f g : PowerSeries R) :
    PowerSeries.coeff 1 (f * g)
      = PowerSeries.constantCoeff f * PowerSeries.coeff 1 g
        + PowerSeries.coeff 1 f * PowerSeries.constantCoeff g := by
  rw [PowerSeries.coeff_mul, show (1 : ℕ) = 0 + 1 from rfl, Finset.Nat.sum_antidiagonal_succ]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_one_X_mul (f : PowerSeries R) :
    PowerSeries.coeff 1 (PowerSeries.X * f) = PowerSeries.constantCoeff f := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end Coeff

section FrakF

variable {R : Type*} [CommRing R]

noncomputable def frakF (i j : ℕ) (S z : R) (r : ℕ) : PowerSeries R :=
  cont (fun t => PowerSeries.C (bdiagE R S z t)
          + PowerSeries.X * PowerSeries.C (ncoef R i j t))
    (fun t => PowerSeries.X * PowerSeries.C (bcoef R i j t))
    (fun t => PowerSeries.C (ccoef R z t)) r

theorem frakF_top (i j : ℕ) (S z : R) :
    frakF i j S z (min i j + 1)
      = frakE (PowerSeries R) i j (PowerSeries.C S) (PowerSeries.C z) PowerSeries.X := by
  rw [frakE_eq_cont, frakF]
  congr 1
  · funext t
    simp only [bdiagE, ncoef, map_add, map_mul, map_natCast]
  · funext t
    simp only [bcoef, map_mul, map_neg, map_natCast, map_ofNat]
  · funext t
    simp only [ccoef, map_neg, map_mul, map_add, map_natCast, map_one]

theorem constantCoeff_frakF (i j : ℕ) (S z : R) (r : ℕ) :
    PowerSeries.constantCoeff (frakF i j S z r) = ∏ t ∈ Finset.range r, (S + z * (t : R)) := by
  rw [frakF, cont_map (PowerSeries.constantCoeff (R := R))]
  have h1 : (fun t => PowerSeries.constantCoeff (PowerSeries.C (bdiagE R S z t)
      + PowerSeries.X * PowerSeries.C (ncoef R i j t))) = fun t => bdiagE R S z t := by
    funext t; simp
  have h2 : (fun t => PowerSeries.constantCoeff
      (PowerSeries.X * PowerSeries.C (bcoef R i j t))) = fun _ : ℕ => (0 : R) := by
    funext t; simp
  rw [h1, h2, cont_of_b_zero]
  rfl

theorem coeff_one_frakF_succ_succ (i j : ℕ) (S z : R) (r : ℕ) :
    PowerSeries.coeff 1 (frakF i j S z (r + 2))
      = (S + z * ((r : R) + 1)) * PowerSeries.coeff 1 (frakF i j S z (r + 1))
        + ncoef R i j (r + 1) * ∏ t ∈ Finset.range (r + 1), (S + z * (t : R))
        - bcoef R i j r * ccoef R z r * ∏ t ∈ Finset.range r, (S + z * (t : R)) := by
  have hcont : frakF i j S z (r + 2)
      = (PowerSeries.C (bdiagE R S z (r + 1))
          + PowerSeries.X * PowerSeries.C (ncoef R i j (r + 1))) * frakF i j S z (r + 1)
        - PowerSeries.X * PowerSeries.C (bcoef R i j r) * PowerSeries.C (ccoef R z r)
          * frakF i j S z r := rfl
  rw [hcont, map_sub, coeff_one_mul]
  have hd0 : PowerSeries.constantCoeff (PowerSeries.C (bdiagE R S z (r + 1))
      + PowerSeries.X * PowerSeries.C (ncoef R i j (r + 1))) = S + z * ((r : R) + 1) := by
    simp [bdiagE]
  have hd1 : PowerSeries.coeff 1 (PowerSeries.C (bdiagE R S z (r + 1))
      + PowerSeries.X * PowerSeries.C (ncoef R i j (r + 1))) = ncoef R i j (r + 1) := by
    rw [map_add, coeff_one_X_mul, PowerSeries.coeff_C]
    simp
  have hw : PowerSeries.X * PowerSeries.C (bcoef R i j r) * PowerSeries.C (ccoef R z r)
      = PowerSeries.X * PowerSeries.C (bcoef R i j r * ccoef R z r) := by
    rw [map_mul]; ring
  rw [hw, coeff_one_mul, hd0, hd1, constantCoeff_frakF, constantCoeff_frakF]
  simp only [map_mul, PowerSeries.constantCoeff_X, zero_mul, coeff_one_X_mul,
    PowerSeries.constantCoeff_C]
  ring

theorem coeff_one_frakF_zero (i j : ℕ) (S z : R) :
    PowerSeries.coeff 1 (frakF i j S z 0) = 0 := by
  rw [frakF]
  simp [cont]

theorem coeff_one_frakF_one (i j : ℕ) (S z : R) :
    PowerSeries.coeff 1 (frakF i j S z 1) = ncoef R i j 0 := by
  rw [frakF]
  change PowerSeries.coeff 1 (PowerSeries.C (bdiagE R S z 0)
    + PowerSeries.X * PowerSeries.C (ncoef R i j 0)) = _
  rw [map_add, coeff_one_X_mul, PowerSeries.coeff_C]
  simp

end FrakF

section AtRoot

variable {k : Type*} [Field k] [CharZero k]

def ucoef (R : Type*) [CommRing R] (i j t : ℕ) : R := (((i - t) * (j - t) : ℕ) : R)

theorem bcoef_eq_neg_two_mul_ucoef (R : Type*) [CommRing R] (i j t : ℕ) :
    bcoef R i j t = -2 * ucoef R i j t := rfl

noncomputable def z0 (S : k) (r : ℕ) : k := -S / ((r : k) + 1)

theorem natCast_succ_ne_zero (r : ℕ) : ((r : k) + 1) ≠ 0 :=
  Nat.cast_add_one_ne_zero r

theorem fibre_at_root (S : k) (r : ℕ) : S + z0 S r * ((r : k) + 1) = 0 := by
  rw [z0]
  field_simp
  ring

theorem fibre_ne_zero (S : k) (hS : S ≠ 0) (r t : ℕ) (ht : t ≠ r + 1) :
    S + z0 S r * (t : k) ≠ 0 := by
  have hden := natCast_succ_ne_zero (k := k) r
  have key : S + z0 S r * (t : k) = S * (((r : k) + 1) - (t : k)) / ((r : k) + 1) := by
    rw [z0]; field_simp; ring
  rw [key]
  refine div_ne_zero (mul_ne_zero hS ?_) hden
  intro hc
  have h2 := sub_eq_zero.mp hc
  have h1 : r + 1 = t := by exact_mod_cast h2
  exact ht h1.symm

theorem z0_ne_zero (S : k) (hS : S ≠ 0) (r : ℕ) : z0 S r ≠ 0 := by
  rw [z0]
  exact div_ne_zero (neg_ne_zero.mpr hS) (natCast_succ_ne_zero r)

theorem prod_fibre_eq_zero (S : k) (r n : ℕ) (hn : r + 1 < n) :
    ∏ t ∈ Finset.range n, (S + z0 S r * (t : k)) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hn) ?_
  rw [show ((r + 1 : ℕ) : k) = (r : k) + 1 from by push_cast; ring]
  exact fibre_at_root S r

theorem prod_fibre_ne_zero (S : k) (hS : S ≠ 0) (r n : ℕ) (hn : n ≤ r + 1) :
    ∏ t ∈ Finset.range n, (S + z0 S r * (t : k)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  exact fibre_ne_zero S hS r t (by have := Finset.mem_range.mp ht; omega)

theorem coeff_one_frakF_succ (i j : ℕ) (S : k) (r : ℕ) :
    PowerSeries.coeff 1 (frakF i j S (z0 S r) (r + 2))
      = (∏ t ∈ Finset.range (r + 1), (S + z0 S r * (t : k)))
        * (ncoef k i j (r + 1) + 2 * ((r : k) + 1) * ucoef k i j r) := by
  rw [coeff_one_frakF_succ_succ, fibre_at_root, bcoef_mul_ccoef]
  have hstep : S + z0 S r * (r : k) = -z0 S r := by
    have h0 := fibre_at_root S r
    linear_combination h0
  rw [Finset.prod_range_succ, hstep]
  simp only [ucoef]
  ring

theorem coeff_one_frakF_succ_two (i j : ℕ) (S : k) (r : ℕ) :
    PowerSeries.coeff 1 (frakF i j S (z0 S r) (r + 3))
      = z0 S r * (∏ t ∈ Finset.range (r + 1), (S + z0 S r * (t : k)))
        * (ncoef k i j (r + 1) + 2 * ((r : k) + 1) * ucoef k i j r
            - 2 * ((r : k) + 2) * ucoef k i j (r + 1)) := by
  have h := coeff_one_frakF_succ_succ i j S (z0 S r) (r + 1)
  rw [show r + 1 + 2 = r + 3 from rfl, show r + 1 + 1 = r + 2 from rfl,
    coeff_one_frakF_succ, bcoef_mul_ccoef, prod_fibre_eq_zero S r (r + 2) (by omega)] at h
  have hstep : S + z0 S r * (((r + 1 : ℕ) : k) + 1) = z0 S r := by
    have h0 := fibre_at_root S r
    push_cast
    linear_combination h0
  rw [h, hstep]
  simp only [ucoef]
  push_cast
  ring

theorem coeff_one_frakF_tail (i j : ℕ) (S : k) (r : ℕ) : ∀ d : ℕ,
    PowerSeries.coeff 1 (frakF i j S (z0 S r) (r + 3 + d))
      = PowerSeries.coeff 1 (frakF i j S (z0 S r) (r + 3))
        * ∏ v ∈ Finset.Ico (r + 3) (r + 3 + d), (S + z0 S r * (v : k)) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have h := coeff_one_frakF_succ_succ i j S (z0 S r) (r + 2 + d)
    rw [show r + 2 + d + 2 = r + 3 + (d + 1) from by omega,
      show r + 2 + d + 1 = r + 3 + d from by omega] at h
    rw [h, prod_fibre_eq_zero S r (r + 3 + d) (by omega),
      prod_fibre_eq_zero S r (r + 2 + d) (by omega), ih,
      show r + 3 + (d + 1) = (r + 3 + d) + 1 from by omega,
      Finset.prod_Ico_succ_top (by omega)]
    have hcast : ((r + 2 + d : ℕ) : k) + 1 = ((r + 3 + d : ℕ) : k) := by push_cast; ring
    rw [hcast]
    ring

noncomputable def Pfib (i j : ℕ) (S : k) (r : ℕ) : k :=
  (∏ t ∈ Finset.range (r + 1), (S + z0 S r * (t : k)))
    * ∏ t ∈ Finset.Ico (r + 2) (min i j + 1), (S + z0 S r * (t : k))

def Gfib (R : Type*) [CommRing R] (i j r : ℕ) : R :=
  ncoef R i j (r + 1) + 2 * ((r : R) + 1) * ucoef R i j r
    - 2 * ((r : R) + 2) * ucoef R i j (r + 1)

theorem Pfib_ne_zero (i j : ℕ) (S : k) (hS : S ≠ 0) (r : ℕ) : Pfib i j S r ≠ 0 := by
  refine mul_ne_zero (prod_fibre_ne_zero S hS r (r + 1) le_rfl) ?_
  refine Finset.prod_ne_zero_iff.mpr fun t ht => ?_
  exact fibre_ne_zero S hS r t (by have := (Finset.mem_Ico.mp ht).1; omega)

theorem coeff_one_frakF_top (i j : ℕ) (S : k) (r : ℕ) (hr : r + 1 ≤ min i j) :
    PowerSeries.coeff 1 (frakF i j S (z0 S r) (min i j + 1)) = Pfib i j S r * Gfib k i j r := by
  rcases eq_or_lt_of_le hr with heq | hlt
  · have hu : ucoef k i j (r + 1) = 0 := by
      have hz : (i - (r + 1)) * (j - (r + 1)) = 0 := by
        rcases Nat.le_total i j with h | h
        · have hmin : min i j = i := Nat.min_eq_left h
          have : i - (r + 1) = 0 := by omega
          rw [this, zero_mul]
        · have hmin : min i j = j := Nat.min_eq_right h
          have : j - (r + 1) = 0 := by omega
          rw [this, mul_zero]
      rw [ucoef, hz]
      simp
    rw [← heq, show r + 1 + 1 = r + 2 from rfl, coeff_one_frakF_succ, Pfib, ← heq, Gfib, hu]
    rw [show r + 1 + 1 = r + 2 from rfl, Finset.Ico_self]
    simp
  · obtain ⟨d, hd⟩ : ∃ d, min i j + 1 = r + 3 + d := ⟨min i j - (r + 2), by omega⟩
    rw [hd, coeff_one_frakF_tail, coeff_one_frakF_succ_two, ← hd, Pfib,
      Finset.prod_eq_prod_Ico_succ_bot (by omega : r + 2 < min i j + 1)]
    have hstep : S + z0 S r * ((r + 2 : ℕ) : k) = z0 S r := by
      have h0 := fibre_at_root S r
      push_cast
      linear_combination h0
    rw [hstep, hd, show r + 2 + 1 = r + 3 from rfl, Gfib]
    ring

noncomputable def frakFP (i j : ℕ) (S : k) : (PowerSeries k)[X] :=
  frakEP (PowerSeries k) i j (PowerSeries.C S) PowerSeries.X

noncomputable def frakG (i j : ℕ) (S : k) : k[X] := frakEP k i j S 0

omit [CharZero k] in
theorem frakFP_map_constantCoeff (i j : ℕ) (S : k) :
    (frakFP i j S).map (PowerSeries.constantCoeff (R := k)) = frakG i j S := by
  rw [frakFP, frakG, frakEP_map]
  simp

omit [CharZero k] in
theorem frakG_eq_prod (i j : ℕ) (S : k) :
    frakG i j S
      = ∏ t ∈ Finset.range (min i j + 1), (Polynomial.C S + Polynomial.X * (t : k[X])) := by
  rw [frakG, frakEP, map_zero]
  exact frakE_at_zero i j (Polynomial.C S) Polynomial.X

omit [CharZero k] in
theorem frakG_eq_C_mul (i j : ℕ) (S : k) :
    frakG i j S
      = Polynomial.C S
        * ∏ t ∈ Finset.Ico 1 (min i j + 1), (Polynomial.C S + Polynomial.X * (t : k[X])) := by
  rw [frakG, frakEP, map_zero]
  exact frakE_at_zero_mul i j (Polynomial.C S) Polynomial.X

omit [CharZero k] in
theorem eval_frakG (i j : ℕ) (S z : k) :
    (frakG i j S).eval z = ∏ t ∈ Finset.range (min i j + 1), (S + z * (t : k)) := by
  rw [frakG_eq_prod, Polynomial.eval_prod]
  simp

theorem natDegree_fibre_factor (S : k) {t : ℕ} (ht : 1 ≤ t) :
    (Polynomial.C S + Polynomial.X * (t : k[X])).natDegree = 1 := by
  have hcast : (Polynomial.C S + Polynomial.X * (t : k[X]))
      = Polynomial.C (t : k) * Polynomial.X + Polynomial.C S := by
    rw [Polynomial.C_eq_natCast]
    ring
  rw [hcast]
  exact Polynomial.natDegree_linear (Nat.cast_ne_zero.mpr (by omega))

theorem fibre_factor_ne_zero (S : k) {t : ℕ} (ht : 1 ≤ t) :
    (Polynomial.C S + Polynomial.X * (t : k[X])) ≠ 0 := by
  intro h
  have hd := natDegree_fibre_factor S ht
  rw [h] at hd
  simp at hd

theorem frakG_ne_zero (i j : ℕ) (S : k) (hS : S ≠ 0) : frakG i j S ≠ 0 := by
  rw [frakG_eq_C_mul]
  refine mul_ne_zero (Polynomial.C_ne_zero.mpr hS) (Finset.prod_ne_zero_iff.mpr fun t ht => ?_)
  exact fibre_factor_ne_zero S (Finset.mem_Ico.mp ht).1

theorem natDegree_frakG (i j : ℕ) (S : k) (hS : S ≠ 0) :
    (frakG i j S).natDegree = min i j := by
  rw [frakG_eq_C_mul, Polynomial.natDegree_C_mul hS,
    Polynomial.natDegree_prod _ _ (fun t ht => fibre_factor_ne_zero S (Finset.mem_Ico.mp ht).1)]
  rw [Finset.sum_congr rfl (fun t ht => natDegree_fibre_factor S (Finset.mem_Ico.mp ht).1)]
  simp

theorem natDegree_frakFP (i j : ℕ) (S : k) (hS : S ≠ 0) :
    (frakFP i j S).natDegree = min i j := by
  refine le_antisymm (natDegree_frakEP_le i j _ _) ?_
  have h := Polynomial.natDegree_map_le (p := frakFP i j S)
    (f := PowerSeries.constantCoeff (R := k))
  rw [frakFP_map_constantCoeff, natDegree_frakG i j S hS] at h
  exact h

theorem constantCoeff_leadingCoeff_frakFP (i j : ℕ) (S : k) (hS : S ≠ 0) :
    PowerSeries.constantCoeff ((frakFP i j S).leadingCoeff) = (frakG i j S).leadingCoeff := by
  have h1 : (frakG i j S).leadingCoeff = (frakG i j S).coeff (min i j) := by
    rw [Polynomial.leadingCoeff, natDegree_frakG i j S hS]
  have h2 : (frakFP i j S).leadingCoeff = (frakFP i j S).coeff (min i j) := by
    rw [Polynomial.leadingCoeff, natDegree_frakFP i j S hS]
  rw [h1, h2, ← frakFP_map_constantCoeff, Polynomial.coeff_map]

theorem isUnit_leadingCoeff_frakFP (i j : ℕ) (S : k) (hS : S ≠ 0) :
    IsUnit ((frakFP i j S).leadingCoeff) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_leadingCoeff_frakFP i j S hS]
  exact (Polynomial.leadingCoeff_ne_zero.mpr (frakG_ne_zero i j S hS)).isUnit

theorem eval_derivative_frakG (i j : ℕ) (S : k) (r : ℕ) (hr : r + 1 ≤ min i j) :
    (Polynomial.derivative (frakG i j S)).eval (z0 S r) = ((r : k) + 1) * Pfib i j S r := by
  set f : ℕ → k[X] := fun t => Polynomial.C S + Polynomial.X * (t : k[X]) with hf
  have hsplit : frakG i j S
      = (∏ t ∈ Finset.range (r + 1), f t)
        * (f (r + 1) * ∏ t ∈ Finset.Ico (r + 2) (min i j + 1), f t) := by
    rw [frakG_eq_prod, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.prod_Ico_consecutive f (Nat.zero_le (r + 1)) (by omega : r + 1 ≤ min i j + 1),
      Finset.prod_eq_prod_Ico_succ_bot (by omega : r + 1 < min i j + 1) f]
  have hd2 : Polynomial.derivative (f (r + 1)) = ((r + 1 : ℕ) : k[X]) := by
    simp [hf]
  have hz : (f (r + 1)).eval (z0 S r) = 0 := by
    simp only [hf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_natCast]
    rw [show ((r + 1 : ℕ) : k) = (r : k) + 1 from by push_cast; ring]
    exact fibre_at_root S r
  rw [hsplit, Polynomial.derivative_mul, Polynomial.derivative_mul]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, hz, mul_zero, zero_mul, add_zero, zero_add,
    hd2, Polynomial.eval_natCast]
  rw [Pfib, show ((r + 1 : ℕ) : k) = (r : k) + 1 from by push_cast; ring]
  simp only [hf, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_natCast]
  ring

omit [CharZero k] in
theorem constantCoeff_eval_C (p : (PowerSeries k)[X]) (x : k) :
    PowerSeries.constantCoeff (p.eval (PowerSeries.C x))
      = (p.map (PowerSeries.constantCoeff (R := k))).eval x := by
  have h := Polynomial.eval_map_apply (f := PowerSeries.constantCoeff (R := k)) (p := p)
    (x := PowerSeries.C x)
  simpa using h.symm

theorem constantCoeff_eval_derivative (i j : ℕ) (S : k) (_hS : S ≠ 0) (r : ℕ)
    (hr : r + 1 ≤ min i j) (v : PowerSeries k) :
    PowerSeries.constantCoeff
        ((Polynomial.derivative (Polynomial.C v * frakFP i j S)).eval (PowerSeries.C (z0 S r)))
      = PowerSeries.constantCoeff v * (((r : k) + 1) * Pfib i j S r) := by
  rw [constantCoeff_eval_C, ← Polynomial.derivative_map, Polynomial.map_mul, Polynomial.map_C,
    frakFP_map_constantCoeff, Polynomial.derivative_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C, eval_derivative_frakG i j S r hr]

omit [CharZero k] in
theorem henselianLocalRing_powerSeries : HenselianLocalRing (PowerSeries k) where
  is_henselian := by
    intro f hf a₀ h₁ h₂
    obtain ⟨a, ha1, ha2⟩ := HenselianRing.is_henselian (R := PowerSeries k)
      (I := Ideal.span {(PowerSeries.X : PowerSeries k)}) f hf a₀
      (by rwa [← PowerSeries.maximalIdeal_eq_span_X]) (h₂.map _)
    exact ⟨a, ha1, by rwa [PowerSeries.maximalIdeal_eq_span_X]⟩

theorem root_exists (i j : ℕ) (S : k) (hS : S ≠ 0) (r : ℕ) (hr : r + 1 ≤ min i j) :
    ∃ ζ : PowerSeries k,
      (frakFP i j S).IsRoot ζ ∧ PowerSeries.constantCoeff ζ = z0 S r := by
  have := henselianLocalRing_powerSeries (k := k)
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_frakFP i j S hS
  set v : PowerSeries k := ((u⁻¹ : (PowerSeries k)ˣ) : PowerSeries k) with hv
  have hvu : v * (frakFP i j S).leadingCoeff = 1 := by
    rw [hv, ← hu]; exact u.inv_mul
  have hvunit : IsUnit v := (u⁻¹).isUnit
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, zero_mul] at hvu
    exact zero_ne_one hvu
  have hmonic : (Polynomial.C v * frakFP i j S).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hvu]
  have hmapf : (Polynomial.C v * frakFP i j S).map (PowerSeries.constantCoeff (R := k))
      = Polynomial.C (PowerSeries.constantCoeff v) * frakG i j S := by
    rw [Polynomial.map_mul, Polynomial.map_C, frakFP_map_constantCoeff]
  have hev : PowerSeries.constantCoeff
      ((Polynomial.C v * frakFP i j S).eval (PowerSeries.C (z0 S r))) = 0 := by
    rw [constantCoeff_eval_C, hmapf, Polynomial.eval_mul, Polynomial.eval_C, eval_frakG,
      prod_fibre_eq_zero S r (min i j + 1) (by omega), mul_zero]
  have hvc : PowerSeries.constantCoeff v ≠ 0 :=
    (hvunit.map (PowerSeries.constantCoeff (R := k))).ne_zero
  have hunit : IsUnit ((Polynomial.derivative (Polynomial.C v * frakFP i j S)).eval
      (PowerSeries.C (z0 S r))) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_eval_derivative i j S hS r hr v]
    refine IsUnit.mk0 _ ?_
    refine mul_ne_zero hvc (mul_ne_zero (natCast_succ_ne_zero r) (Pfib_ne_zero i j S hS r))
  obtain ⟨a, ha1, ha2⟩ := HenselianLocalRing.is_henselian (R := PowerSeries k)
    (Polynomial.C v * frakFP i j S) hmonic (PowerSeries.C (z0 S r))
    (by
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
      exact hev)
    hunit
  refine ⟨a, ?_, ?_⟩
  · have h0 : Polynomial.eval a (Polynomial.C v * frakFP i j S) = 0 := ha1
    rw [Polynomial.eval_mul, Polynomial.eval_C] at h0
    exact (mul_eq_zero.mp h0).resolve_left hv0
  · rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
      map_sub, PowerSeries.constantCoeff_C] at ha2
    exact sub_eq_zero.mp ha2

theorem root_coeff_one (i j : ℕ) (S : k) (hS : S ≠ 0) (r : ℕ) (hr : r + 1 ≤ min i j)
    {ζ : PowerSeries k} (hroot : (frakFP i j S).IsRoot ζ)
    (h0 : PowerSeries.constantCoeff ζ = z0 S r) :
    PowerSeries.coeff 1 ζ = -Gfib k i j r / ((r : k) + 1) := by
  obtain ⟨w, hw⟩ : (PowerSeries.X : PowerSeries k) ∣ (ζ - PowerSeries.C (z0 S r)) := by
    rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, h0, sub_self]
  have hζ : PowerSeries.C (z0 S r) + PowerSeries.X * w = ζ := by
    rw [← hw]; ring
  have hζ1 : PowerSeries.coeff 1 ζ = PowerSeries.constantCoeff w := by
    rw [← hζ, map_add, coeff_one_X_mul, PowerSeries.coeff_C]
    simp
  obtain ⟨c, hc⟩ := (frakFP i j S).binomExpansion (PowerSeries.C (z0 S r)) (PowerSeries.X * w)
  have hroot' : Polynomial.eval ζ (frakFP i j S) = 0 := hroot
  rw [hζ, hroot'] at hc
  have hA : PowerSeries.coeff 1 ((frakFP i j S).eval (PowerSeries.C (z0 S r)))
      = Pfib i j S r * Gfib k i j r := by
    rw [frakFP, frakEP_eval, ← frakF_top, coeff_one_frakF_top i j S r hr]
  have hB : PowerSeries.coeff 1
      ((Polynomial.derivative (frakFP i j S)).eval (PowerSeries.C (z0 S r))
        * (PowerSeries.X * w))
      = (((r : k) + 1) * Pfib i j S r) * PowerSeries.constantCoeff w := by
    have hcomm : (Polynomial.derivative (frakFP i j S)).eval (PowerSeries.C (z0 S r))
        * (PowerSeries.X * w)
        = PowerSeries.X * ((Polynomial.derivative (frakFP i j S)).eval
            (PowerSeries.C (z0 S r)) * w) := by ring
    rw [hcomm, coeff_one_X_mul, map_mul]
    congr 1
    have hone := constantCoeff_eval_derivative i j S hS r hr (1 : PowerSeries k)
    rw [Polynomial.C_1, one_mul, map_one, one_mul] at hone
    exact hone
  have hC : PowerSeries.coeff 1 (c * (PowerSeries.X * w) ^ 2) = 0 := by
    have hdvd : (PowerSeries.X : PowerSeries k) ^ 2 ∣ c * (PowerSeries.X * w) ^ 2 :=
      ⟨c * w ^ 2, by ring⟩
    exact (PowerSeries.X_pow_dvd_iff.mp hdvd) 1 (by omega)
  have hkey := congrArg (PowerSeries.coeff (R := k) 1) hc
  rw [map_zero, map_add, map_add, hA, hB, hC, add_zero] at hkey
  have hP := Pfib_ne_zero i j S hS r
  have hr1 := natCast_succ_ne_zero (k := k) r
  rw [hζ1]
  field_simp
  have hfinal : Pfib i j S r
      * (Gfib k i j r + ((r : k) + 1) * PowerSeries.constantCoeff w) = 0 := by
    rw [mul_add]
    linear_combination -hkey
  rcases mul_eq_zero.mp hfinal with h | h
  · exact absurd h hP
  · linear_combination h

open scoped Classical in
noncomputable def zetaRoot (i j : ℕ) (S : k) (r : ℕ) : PowerSeries k :=
  if h : S ≠ 0 ∧ r + 1 ≤ min i j then (root_exists i j S h.1 r h.2).choose else 0

theorem zetaRoot_isRoot (i j : ℕ) (S : k) (hS : S ≠ 0) (r : ℕ) (hr : r + 1 ≤ min i j) :
    (frakFP i j S).IsRoot (zetaRoot i j S r) := by
  rw [zetaRoot, dite_eq_left ⟨hS, hr⟩]
  exact (root_exists i j S hS r hr).choose_spec.1

theorem zetaRoot_constantCoeff (i j : ℕ) (S : k) (hS : S ≠ 0) (r : ℕ) (hr : r + 1 ≤ min i j) :
    PowerSeries.constantCoeff (zetaRoot i j S r) = z0 S r := by
  rw [zetaRoot, dite_eq_left ⟨hS, hr⟩]
  exact (root_exists i j S hS r hr).choose_spec.2

theorem zetaRoot_coeff_one (i j : ℕ) (S : k) (hS : S ≠ 0) (r : ℕ) (hr : r + 1 ≤ min i j) :
    PowerSeries.coeff 1 (zetaRoot i j S r) = -Gfib k i j r / ((r : k) + 1) :=
  root_coeff_one i j S hS r hr (zetaRoot_isRoot i j S hS r hr)
    (zetaRoot_constantCoeff i j S hS r hr)

end AtRoot

end Rhone.Analysis.Rescale
