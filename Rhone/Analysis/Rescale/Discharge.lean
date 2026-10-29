/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.Rescale.Hensel
public import Rhone.Analysis.DenominatorEquation.Separation
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.CharP.Algebra

/-! # Block separation of the roots of `E_{i,j}` after rescaling, splitting discharged -/

@[expose] public section

namespace Rhone.Analysis.Rescale

open Polynomial LinearAlgebra.Tridiag DenominatorEquation

section Zone

variable {F : Type*} [Field F]

def z1 (a b t : F) : F :=
  -((a + b + t) * (a + b + t - 1) - 2 * (t + 1) * (a * b) + 2 * t * (a + 1) * (b + 1)) / t

theorem z1_eq_z1sep (a b t : ℚ) : z1 a b t = z1sep a b t := rfl

theorem z1_map {F' : Type*} [Field F'] (f : F →+* F') (a b t : F) :
    z1 (f a) (f b) (f t) = f (z1 a b t) := by
  simp only [z1, map_div₀, map_neg, map_add, map_sub, map_mul, map_one, map_ofNat]

end Zone

section Gfib

variable {k : Type*} [Field k] [CharZero k]

omit [CharZero k] in
theorem z1_eq_neg_Gfib_div (i j r : ℕ) (hr : r + 1 ≤ min i j) :
    z1 ((i : k) - ((r : k) + 1)) ((j : k) - ((r : k) + 1)) ((r : k) + 1)
      = -Gfib k i j r / ((r : k) + 1) := by
  have hi : r + 1 ≤ i := le_trans hr (Nat.min_le_left i j)
  have hj : r + 1 ≤ j := le_trans hr (Nat.min_le_right i j)
  have e1 : (((i + j - (r + 1)) : ℕ) : k) = (i : k) + (j : k) - ((r : k) + 1) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have e2 : (((i + j - (r + 1) - 1) : ℕ) : k) = (i : k) + (j : k) - ((r : k) + 1) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ i + j - (r + 1)), e1, Nat.cast_one]
  have c1 : (((i + j - (r + 1)) * (i + j - (r + 1) - 1) : ℕ) : k)
      = ((i : k) + (j : k) - ((r : k) + 1)) * ((i : k) + (j : k) - ((r : k) + 1) - 1) := by
    rw [Nat.cast_mul, e1, e2]
  have c3 : (((i - (r + 1)) * (j - (r + 1)) : ℕ) : k)
      = ((i : k) - ((r : k) + 1)) * ((j : k) - ((r : k) + 1)) := by
    rw [Nat.cast_mul, Nat.cast_sub hi, Nat.cast_sub hj]
    push_cast
    ring
  have c4 : (((i - r) * (j - r) : ℕ) : k) = ((i : k) - (r : k)) * ((j : k) - (r : k)) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  rw [z1, Gfib, ncoef, ucoef, ucoef, c1, c3, c4]
  ring

end Gfib

section Split

variable {L : Type*} [Field L] {ι : Type*}

theorem split_of_roots {p : L[X]} {s : Finset ι} {α : ι → L} (hp : p ≠ 0)
    (hroot : ∀ t ∈ s, p.IsRoot (α t)) (hinj : Set.InjOn α s) (hdeg : p.natDegree ≤ s.card) :
    p = Polynomial.C p.leadingCoeff * ∏ t ∈ s, (X - Polynomial.C (α t)) := by
  classical
  have hmonic : (∏ t ∈ s, (X - Polynomial.C (α t))).Monic :=
    monic_prod_of_monic _ _ fun t _ => monic_X_sub_C (α t)
  have hdvd : (∏ t ∈ s, (X - Polynomial.C (α t))) ∣ p := by
    refine Finset.prod_dvd_of_coprime (fun a ha c hc hac => ?_) fun t ht => ?_
    · exact isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero_of_ne fun h => hac (hinj ha hc h)).isUnit
    · exact (Polynomial.dvd_iff_isRoot).mpr (hroot t ht)
  obtain ⟨h, hh⟩ := hdvd
  have hdegprod : (∏ t ∈ s, (X - Polynomial.C (α t))).natDegree = s.card := by
    rw [Polynomial.natDegree_prod _ _ fun t _ => (monic_X_sub_C (α t)).ne_zero]
    simp
  have hh0 : h ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hh
    exact hp hh
  have hdegh : h.natDegree = 0 := by
    have := congrArg Polynomial.natDegree hh
    rw [Polynomial.natDegree_mul hmonic.ne_zero hh0, hdegprod] at this
    omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegh
  have hlead : p.leadingCoeff = c := by
    rw [hh, ← hc, Polynomial.leadingCoeff_mul, hmonic.leadingCoeff, Polynomial.leadingCoeff_C,
      one_mul]
  rw [hlead, hh, ← hc]
  ring

end Split

section Descent

variable {K L : Type*} [Field K] [Field L]

theorem squarefree_of_map (f : K →+* L) {p : K[X]} (h : Squarefree (p.map f)) : Squarefree p := by
  intro q hq
  have hmap : (q.map f) * (q.map f) ∣ p.map f := by
    rw [← Polynomial.map_mul]
    exact Polynomial.map_dvd _ hq
  have hu := h (q.map f) hmap
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hu ⊢
  rwa [Polynomial.degree_map_eq_of_injective f.injective] at hu

end Descent

section Laurent

variable {k : Type*} [Field k] [CharZero k]

abbrev LaurentK (k : Type*) [Field k] := FractionRing (PowerSeries k)

noncomputable def sig (k : Type*) [Field k] : LaurentK k :=
  algebraMap (PowerSeries k) (LaurentK k) PowerSeries.X

noncomputable def kToL (k : Type*) [Field k] : k →+* LaurentK k :=
  (algebraMap (PowerSeries k) (LaurentK k)).comp (PowerSeries.C (R := k))

omit [CharZero k] in
theorem algebraMap_injective_powerSeries :
    Function.Injective (algebraMap (PowerSeries k) (LaurentK k)) :=
  IsFractionRing.injective (PowerSeries k) (LaurentK k)

omit [CharZero k] in
theorem sig_ne_zero : sig k ≠ 0 := by
  rw [sig, Ne, map_eq_zero_iff _ algebraMap_injective_powerSeries]
  intro h
  have h1 : PowerSeries.coeff (R := k) 1 PowerSeries.X = 1 := PowerSeries.coeff_one_X
  rw [h, map_zero] at h1
  exact zero_ne_one h1

omit [CharZero k] in
theorem sig_mul_inv : sig k * (sig k)⁻¹ = 1 := mul_inv_cancel₀ sig_ne_zero

omit [CharZero k] in
theorem div_sig_mul_sig (x : LaurentK k) : x / sig k * sig k = x := by
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self sig_ne_zero, mul_one]

noncomputable def thetaA (k : Type*) [Field k] : LaurentK k := (sig k)⁻¹

noncomputable def thetaB {k : Type*} [Field k] (b : k) : LaurentK k := kToL k b * (sig k)⁻¹

def Sval {k : Type*} [Field k] (i j : ℕ) (b : k) : k := (i : k) + (j : k) * b

omit [CharZero k] in
theorem kToL_Sval (i j : ℕ) (b : k) :
    kToL k (Sval i j b) = (i : LaurentK k) + (j : LaurentK k) * kToL k b := by
  rw [Sval, map_add, map_mul, map_natCast, map_natCast]

omit [CharZero k] in
theorem sigma_pow_mul_E_laurent (i j : ℕ) (b : k) :
    (Polynomial.C (sig k)) ^ (min i j + 1)
        * E (LaurentK k)[X] i j (Polynomial.C (thetaA k)) (Polynomial.C (thetaB b)) Polynomial.X
      = frakE (LaurentK k)[X] i j (Polynomial.C (kToL k (Sval i j b)))
          (Polynomial.C (sig k) * Polynomial.X) (Polynomial.C (sig k)) := by
  have hA : Polynomial.C (sig k) * Polynomial.C (thetaA k) = 1 := by
    rw [← Polynomial.C_mul, thetaA, sig_mul_inv, Polynomial.C_1]
  have hB : Polynomial.C (sig k) * Polynomial.C (thetaB b) = Polynomial.C (kToL k b) := by
    rw [← Polynomial.C_mul, thetaB, ← mul_assoc, mul_comm (sig k) (kToL k b), mul_assoc,
      sig_mul_inv, mul_one]
  have h := sigma_pow_mul_E (R := (LaurentK k)[X]) i j (Polynomial.C (thetaA k))
    (Polynomial.C (thetaB b)) Polynomial.X (Polynomial.C (kToL k b))
    (Polynomial.C (sig k) * Polynomial.X) (Polynomial.C (sig k)) hA hB rfl
  have hSC : (Polynomial.C (kToL k (Sval i j b)) : (LaurentK k)[X])
      = (i : (LaurentK k)[X]) + (j : (LaurentK k)[X]) * Polynomial.C (kToL k b) := by
    rw [kToL_Sval, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_eq_natCast,
      Polynomial.C_eq_natCast]
  rw [h, hSC]

omit [CharZero k] in
theorem frakE_laurent_eq_comp (i j : ℕ) (S : k) :
    frakE (LaurentK k)[X] i j (Polynomial.C (kToL k S)) (Polynomial.C (sig k) * Polynomial.X)
        (Polynomial.C (sig k))
      = ((frakFP i j S).map (algebraMap (PowerSeries k) (LaurentK k))).comp
          (Polynomial.C (sig k) * Polynomial.X) := by
  rw [frakFP, frakEP_map]
  have hS : (algebraMap (PowerSeries k) (LaurentK k)) (PowerSeries.C S) = kToL k S := rfl
  have hX : (algebraMap (PowerSeries k) (LaurentK k)) PowerSeries.X = sig k := rfl
  have hhom : ∀ p : (LaurentK k)[X],
      Polynomial.eval₂ (Polynomial.C : LaurentK k →+* (LaurentK k)[X])
          (Polynomial.C (sig k) * Polynomial.X) p
        = (Polynomial.eval₂RingHom (Polynomial.C : LaurentK k →+* (LaurentK k)[X])
            (Polynomial.C (sig k) * Polynomial.X)) p := fun _ => rfl
  rw [hS, hX, frakEP, Polynomial.comp, hhom,
    frakE_map (Polynomial.eval₂RingHom (Polynomial.C : LaurentK k →+* (LaurentK k)[X])
      (Polynomial.C (sig k) * Polynomial.X))]
  norm_num

noncomputable def rhoRoot (i j : ℕ) (b : k) (r : ℕ) : LaurentK k :=
  algebraMap (PowerSeries k) (LaurentK k) (zetaRoot i j (Sval i j b) r) / sig k

noncomputable def Epoly (i j : ℕ) (b : k) : (LaurentK k)[X] :=
  E (LaurentK k)[X] i j (Polynomial.C (thetaA k)) (Polynomial.C (thetaB b)) Polynomial.X

theorem frakFP_ne_zero (i j : ℕ) (S : k) (hS : S ≠ 0) : frakFP i j S ≠ 0 := by
  intro h
  have := isUnit_leadingCoeff_frakFP i j S hS
  rw [h] at this
  simp at this

theorem Epoly_ne_zero (i j : ℕ) (b : k) (hS : Sval i j b ≠ 0) : Epoly i j b ≠ 0 := by
  intro h
  have hmain := sigma_pow_mul_E_laurent i j b
  rw [← Epoly, h, mul_zero, frakE_laurent_eq_comp] at hmain
  have hback : ((frakFP i j (Sval i j b)).map
      (algebraMap (PowerSeries k) (LaurentK k))) = 0 := by
    have hcomp := congrArg (fun p : (LaurentK k)[X] =>
      p.comp (Polynomial.C (sig k)⁻¹ * Polynomial.X)) hmain.symm
    simp only [Polynomial.zero_comp] at hcomp
    rw [Polynomial.comp_assoc] at hcomp
    have hid : (Polynomial.C (sig k) * Polynomial.X).comp
        (Polynomial.C (sig k)⁻¹ * Polynomial.X) = Polynomial.X := by
      rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
        ← Polynomial.C_mul, sig_mul_inv, Polynomial.C_1, one_mul]
    rw [hid, Polynomial.comp_X] at hcomp
    exact hcomp
  rw [Polynomial.map_eq_zero_iff algebraMap_injective_powerSeries] at hback
  exact frakFP_ne_zero i j (Sval i j b) hS hback

theorem natDegree_Epoly_le (i j : ℕ) (b : k) (hS : Sval i j b ≠ 0) :
    (Epoly i j b).natDegree ≤ min i j := by
  have hmain := sigma_pow_mul_E_laurent i j b
  rw [← Epoly, frakE_laurent_eq_comp] at hmain
  have hpow : (Polynomial.C (sig k)) ^ (min i j + 1)
      = Polynomial.C ((sig k) ^ (min i j + 1)) := Polynomial.C_pow.symm
  have hd := congrArg Polynomial.natDegree hmain
  rw [hpow, Polynomial.natDegree_C_mul (pow_ne_zero _ sig_ne_zero), Polynomial.natDegree_comp,
    Polynomial.natDegree_map_eq_of_injective algebraMap_injective_powerSeries,
    natDegree_frakFP i j (Sval i j b) hS, Polynomial.natDegree_C_mul_X _ sig_ne_zero] at hd
  omega

theorem Epoly_isRoot (i j : ℕ) (b : k) (hS : Sval i j b ≠ 0) (r : ℕ) (hr : r + 1 ≤ min i j) :
    (Epoly i j b).IsRoot (rhoRoot i j b r) := by
  have hmain := sigma_pow_mul_E_laurent i j b
  rw [← Epoly, frakE_laurent_eq_comp] at hmain
  have hev := congrArg (fun p : (LaurentK k)[X] => p.eval (rhoRoot i j b r)) hmain
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_X] at hev
  have hz : sig k * rhoRoot i j b r
      = algebraMap (PowerSeries k) (LaurentK k) (zetaRoot i j (Sval i j b) r) := by
    rw [rhoRoot, mul_div_cancel₀ _ sig_ne_zero]
  rw [hz, Polynomial.eval_map_apply] at hev
  have hroot : Polynomial.eval (zetaRoot i j (Sval i j b) r) (frakFP i j (Sval i j b)) = 0 :=
    zetaRoot_isRoot i j (Sval i j b) hS r hr
  rw [hroot, map_zero] at hev
  have := (mul_eq_zero.mp hev).resolve_left (pow_ne_zero _ sig_ne_zero)
  exact this

omit [CharZero k] in
theorem Sval_ne_zero (i j : ℕ) (b : k)
    (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0) (hi : 1 ≤ i) :
    Sval i j b ≠ 0 := by
  intro h
  have hz : ((i : ℤ) : k) + ((j : ℤ) : k) * b = 0 := by
    push_cast
    rw [Sval] at h
    exact h
  have := (hb (i : ℤ) (j : ℤ) hz).1
  omega

theorem rhoRoot_injOn (i j : ℕ) (b : k) (hS : Sval i j b ≠ 0) :
    Set.InjOn (rhoRoot i j b) (Finset.range (min i j)) := by
  intro r hr r' hr' h
  have hrm : r + 1 ≤ min i j := by
    have := Finset.mem_range.mp (by exact_mod_cast hr); omega
  have hrm' : r' + 1 ≤ min i j := by
    have := Finset.mem_range.mp (by exact_mod_cast hr'); omega
  have h2 : algebraMap (PowerSeries k) (LaurentK k) (zetaRoot i j (Sval i j b) r)
      = algebraMap (PowerSeries k) (LaurentK k) (zetaRoot i j (Sval i j b) r') := by
    have hmul := congrArg (fun x : LaurentK k => x * sig k) h
    simpa only [rhoRoot, div_sig_mul_sig] using hmul
  have h3 := algebraMap_injective_powerSeries h2
  have h4 : z0 (Sval i j b) r = z0 (Sval i j b) r' := by
    rw [← zetaRoot_constantCoeff i j (Sval i j b) hS r hrm,
      ← zetaRoot_constantCoeff i j (Sval i j b) hS r' hrm', h3]
  rw [z0, z0, div_eq_div_iff (natCast_succ_ne_zero r) (natCast_succ_ne_zero r')] at h4
  have h5 : ((r' : k) + 1) = ((r : k) + 1) :=
    mul_left_cancel₀ (neg_ne_zero.mpr hS) h4
  have h6 : (r' : k) = (r : k) := add_right_cancel h5
  exact (Nat.cast_injective h6).symm

theorem Epoly_split (i j : ℕ) (b : k) (hS : Sval i j b ≠ 0) :
    Epoly i j b = Polynomial.C (Epoly i j b).leadingCoeff
      * ∏ r ∈ Finset.range (min i j), (Polynomial.X - Polynomial.C (rhoRoot i j b r)) :=
  split_of_roots (Epoly_ne_zero i j b hS)
    (fun r hr => Epoly_isRoot i j b hS r (by have := Finset.mem_range.mp hr; omega))
    (rhoRoot_injOn i j b hS)
    (by rw [Finset.card_range]; exact natDegree_Epoly_le i j b hS)

theorem E_squarefree_laurent (i j : ℕ) (b : k)
    (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0) (hi : 1 ≤ i) :
    Squarefree (Epoly i j b) := by
  have hS := Sval_ne_zero i j b hb hi
  exact squarefree_of_split (Polynomial.leadingCoeff_ne_zero.mpr (Epoly_ne_zero i j b hS))
    (Epoly_split i j b hS) (rhoRoot_injOn i j b hS)

theorem separation_from_roots (i j p q r r' : ℕ) (b : k)
    (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0)
    (hri : r + 1 ≤ min i j) (hrp : r' + 1 ≤ min p q)
    (h0 : z0 (Sval i j b) r = z0 (Sval p q b) r')
    (h1 : -Gfib k i j r / ((r : k) + 1) = -Gfib k p q r' / ((r' : k) + 1)) :
    p = i ∧ q = j := by
  have hti : r + 1 ≤ i := le_trans hri (Nat.min_le_left i j)
  have htj : r + 1 ≤ j := le_trans hri (Nat.min_le_right i j)
  rw [z0, z0, div_eq_div_iff (natCast_succ_ne_zero r) (natCast_succ_ne_zero r')] at h0
  have hzint : (((i : ℤ) * ((r' : ℤ) + 1) - (p : ℤ) * ((r : ℤ) + 1) : ℤ) : k)
      + (((j : ℤ) * ((r' : ℤ) + 1) - (q : ℤ) * ((r : ℤ) + 1) : ℤ) : k) * b = 0 := by
    push_cast
    rw [Sval, Sval] at h0
    linear_combination -h0
  obtain ⟨hc, hd⟩ := hb _ _ hzint
  have hpn : i * (r' + 1) = p * (r + 1) := by
    have : (i : ℤ) * ((r' : ℤ) + 1) = (p : ℤ) * ((r : ℤ) + 1) := by omega
    exact_mod_cast this
  have hqn : j * (r' + 1) = q * (r + 1) := by
    have : (j : ℤ) * ((r' : ℤ) + 1) = (q : ℤ) * ((r : ℤ) + 1) := by omega
    exact_mod_cast this
  have hcast : ∀ a c t : ℚ,
      ((z1 a c t : ℚ) : k) = z1 ((a : ℚ) : k) ((c : ℚ) : k) ((t : ℚ) : k) := by
    intro a c t
    have hz := z1_map (Rat.castHom k) a c t
    simpa using hz.symm
  have hQ : z1sep ((p : ℚ) - ((r' + 1 : ℕ) : ℚ)) ((q : ℚ) - ((r' + 1 : ℕ) : ℚ))
        (((r' + 1 : ℕ) : ℚ))
      = z1sep ((i : ℚ) - ((r + 1 : ℕ) : ℚ)) ((j : ℚ) - ((r + 1 : ℕ) : ℚ))
        (((r + 1 : ℕ) : ℚ)) := by
    rw [← z1_eq_z1sep, ← z1_eq_z1sep]
    refine Rat.cast_injective (α := k) ?_
    rw [hcast, hcast]
    push_cast
    rw [z1_eq_neg_Gfib_div (k := k) p q r' hrp, z1_eq_neg_Gfib_div (k := k) i j r hri]
    exact h1.symm
  obtain ⟨h2, h3, _⟩ := separation_core (F := ℚ) (i := i) (j := j) (p := p) (q := q)
    (t := r + 1) (t' := r' + 1) (by omega) (by omega) hti htj hpn hqn hQ
  exact ⟨h2, h3⟩

theorem E_coprime_of_ne_laurent (i j p q : ℕ) (b : k)
    (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0)
    (hi : 1 ≤ i) (_hj : 1 ≤ j) (hp : 1 ≤ p) (_hq : 1 ≤ q) (hne : (i, j) ≠ (p, q)) :
    IsCoprime (Epoly i j b) (Epoly p q b) := by
  have hS := Sval_ne_zero i j b hb hi
  have hS' := Sval_ne_zero p q b hb hp
  refine isCoprime_of_split (Polynomial.leadingCoeff_ne_zero.mpr (Epoly_ne_zero i j b hS))
    (Polynomial.leadingCoeff_ne_zero.mpr (Epoly_ne_zero p q b hS'))
    (Epoly_split i j b hS) (Epoly_split p q b hS') ?_
  intro r hr r' hr' hcon
  have hri : r + 1 ≤ min i j := by have := Finset.mem_range.mp hr; omega
  have hrp : r' + 1 ≤ min p q := by have := Finset.mem_range.mp hr'; omega
  have h2 : algebraMap (PowerSeries k) (LaurentK k) (zetaRoot i j (Sval i j b) r)
      = algebraMap (PowerSeries k) (LaurentK k) (zetaRoot p q (Sval p q b) r') := by
    have hmul := congrArg (fun x : LaurentK k => x * sig k) hcon
    simpa only [rhoRoot, div_sig_mul_sig] using hmul
  have h3 := algebraMap_injective_powerSeries h2
  have h0 : z0 (Sval i j b) r = z0 (Sval p q b) r' := by
    rw [← zetaRoot_constantCoeff i j (Sval i j b) hS r hri,
      ← zetaRoot_constantCoeff p q (Sval p q b) hS' r' hrp, h3]
  have h1 : -Gfib k i j r / ((r : k) + 1) = -Gfib k p q r' / ((r' : k) + 1) := by
    rw [← zetaRoot_coeff_one i j (Sval i j b) hS r hri,
      ← zetaRoot_coeff_one p q (Sval p q b) hS' r' hrp, h3]
  obtain ⟨h4, h5⟩ := separation_from_roots i j p q r r' b hb hri hrp h0 h1
  exact hne (by rw [h4, h5])

variable {K : Type*} [Field K]

omit [CharZero k] in
theorem Epoly_map (θA θB : K) (b : k) (f : K →+* LaurentK k) (hfA : f θA = thetaA k)
    (hfB : f θB = thetaB b) (i j : ℕ) :
    (E K[X] i j (Polynomial.C θA) (Polynomial.C θB) Polynomial.X).map f = Epoly i j b := by
  have h := E_map (Polynomial.mapRingHom f) i j (Polynomial.C θA) (Polynomial.C θB) Polynomial.X
  rw [Polynomial.coe_mapRingHom] at h
  rw [h, Epoly]
  simp only [Polynomial.map_C, Polynomial.map_X, hfA, hfB]

theorem E_squarefree (θA θB : K) (b : k) (f : K →+* LaurentK k) (hfA : f θA = thetaA k)
    (hfB : f θB = thetaB b) (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0)
    (i j : ℕ) (hi : 1 ≤ i) (_hj : 1 ≤ j) :
    Squarefree (E K[X] i j (Polynomial.C θA) (Polynomial.C θB) Polynomial.X) := by
  refine squarefree_of_map f ?_
  rw [Epoly_map θA θB b f hfA hfB i j]
  exact E_squarefree_laurent i j b hb hi

theorem E_coprime_of_ne (θA θB : K) (b : k) (f : K →+* LaurentK k) (hfA : f θA = thetaA k)
    (hfB : f θB = thetaB b) (hb : ∀ c d : ℤ, (c : k) + (d : k) * b = 0 → c = 0 ∧ d = 0)
    (i j p q : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : 1 ≤ p) (hq : 1 ≤ q) (hne : (i, j) ≠ (p, q)) :
    IsCoprime (E K[X] i j (Polynomial.C θA) (Polynomial.C θB) Polynomial.X)
      (E K[X] p q (Polynomial.C θA) (Polynomial.C θB) Polynomial.X) := by
  rw [← Polynomial.isCoprime_map f, Epoly_map θA θB b f hfA hfB i j,
    Epoly_map θA θB b f hfA hfB p q]
  exact E_coprime_of_ne_laurent i j p q b hb hi hj hp hq hne

end Laurent

section Witness

noncomputable def qb : FractionRing (Polynomial ℚ) :=
  algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X

theorem charZero_qb : CharZero (FractionRing (Polynomial ℚ)) :=
  charZero_of_injective_algebraMap
    (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))

theorem qb_transcendental (c d : ℤ)
    (h : (c : FractionRing (Polynomial ℚ)) + (d : FractionRing (Polynomial ℚ)) * qb = 0) :
    c = 0 ∧ d = 0 := by
  have hmap : (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
      ((c : Polynomial ℚ) + (d : Polynomial ℚ) * Polynomial.X) = 0 := by
    rw [map_add, map_mul, map_intCast, map_intCast]
    exact h
  have hz : ((c : Polynomial ℚ) + (d : Polynomial ℚ) * Polynomial.X) = 0 :=
    IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ))
      (by rw [hmap, map_zero])
  rw [← Polynomial.C_eq_intCast, ← Polynomial.C_eq_intCast] at hz
  constructor
  · have h0 := congrArg (fun p : Polynomial ℚ => p.coeff 0) hz
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_zero, Polynomial.coeff_zero, mul_zero, add_zero] at h0
    exact_mod_cast h0
  · have h1 := congrArg (fun p : Polynomial ℚ => p.coeff 1) hz
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_one, Polynomial.coeff_zero, mul_one, one_ne_zero, ite_false,
      zero_add] at h1
    exact_mod_cast h1

end Witness

end Rhone.Analysis.Rescale
