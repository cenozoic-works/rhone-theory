/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Basic

/-! # Rescaled determinant `𝔈 = det (B + σ C)` of the tridiagonal system -/

@[expose] public section

namespace Rhone.Analysis.Rescale

open Matrix Polynomial LinearAlgebra.Tridiag DenominatorEquation

variable (R : Type*) [CommRing R]

def ncoef (i j : ℕ) (t : ℕ) : R := (((i + j - t) * (i + j - t - 1) : ℕ) : R)

def bdiagE (S z : R) (t : ℕ) : R := S + z * t

def Bmat (i j : ℕ) (S z : R) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (bdiagE R S z) (fun _ => 0) (ccoef R z) (min i j + 1)

def Cmat (i j : ℕ) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (ncoef R i j) (bcoef R i j) (fun _ => 0) (min i j + 1)

def frakE (i j : ℕ) (S z σ : R) : R := (Bmat R i j S z + σ • Cmat R i j).det

variable {R}

@[simp]
theorem Bmat_apply (i j : ℕ) (S z : R) (p q : Fin (min i j + 1)) :
    Bmat R i j S z p q = tridEntry (bdiagE R S z) (fun _ => 0) (ccoef R z) (p : ℕ) (q : ℕ) := rfl

@[simp]
theorem Cmat_apply (i j : ℕ) (p q : Fin (min i j + 1)) :
    Cmat R i j p q = tridEntry (ncoef R i j) (bcoef R i j) (fun _ => 0) (p : ℕ) (q : ℕ) := rfl

theorem Bmat_add_smul_Cmat (i j : ℕ) (S z σ : R) :
    Bmat R i j S z + σ • Cmat R i j
      = trid (fun t => bdiagE R S z t + σ * ncoef R i j t) (fun t => σ * bcoef R i j t)
          (ccoef R z) (min i j + 1) := by
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, Bmat_apply, Cmat_apply, trid_apply, smul_eq_mul,
    tridEntry]
  split_ifs <;> ring

theorem frakE_eq_cont (i j : ℕ) (S z σ : R) :
    frakE R i j S z σ
      = cont (fun t => bdiagE R S z t + σ * ncoef R i j t) (fun t => σ * bcoef R i j t)
          (ccoef R z) (min i j + 1) := by
  rw [frakE, Bmat_add_smul_Cmat, det_trid_eq_cont]

theorem sigma_pow_mul_cont (i j : ℕ) (s ρ S z σ : R) (hs : σ * s = S) (hρ : σ * ρ = z) :
    ∀ r : ℕ, σ ^ r * cont (dcoefS R i j s ρ) (bcoef R i j) (ccoef R ρ) r
      = cont (fun t => bdiagE R S z t + σ * ncoef R i j t) (fun t => σ * bcoef R i j t)
          (ccoef R z) r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [cont]
    | 1 =>
      simp only [cont, pow_one, dcoefS, bdiagE, ncoef, Nat.cast_zero, mul_zero, add_zero]
      rw [← hs]
      ring
    | (r + 2) =>
      rw [cont, cont, mul_sub, ← ih (r + 1) (by omega), ← ih r (by omega)]
      have h1 : σ ^ (r + 2) * (dcoefS R i j s ρ (r + 1) * cont (dcoefS R i j s ρ) (bcoef R i j)
          (ccoef R ρ) (r + 1))
          = (bdiagE R S z (r + 1) + σ * ncoef R i j (r + 1))
            * (σ ^ (r + 1) * cont (dcoefS R i j s ρ) (bcoef R i j) (ccoef R ρ) (r + 1)) := by
        rw [dcoefS, bdiagE, ncoef, ← hs, ← hρ]
        ring
      have h2 : σ ^ (r + 2) * (bcoef R i j r * ccoef R ρ r
            * cont (dcoefS R i j s ρ) (bcoef R i j) (ccoef R ρ) r)
          = σ * bcoef R i j r * ccoef R z r
            * (σ ^ r * cont (dcoefS R i j s ρ) (bcoef R i j) (ccoef R ρ) r) := by
        rw [ccoef, ccoef, ← hρ]
        ring
      rw [h1, h2]

theorem sigma_pow_mul_ES (i j : ℕ) (s ρ S z σ : R) (hs : σ * s = S) (hρ : σ * ρ = z) :
    σ ^ (min i j + 1) * ES R i j s ρ = frakE R i j S z σ := by
  rw [ES_eq_cont, frakE_eq_cont, sigma_pow_mul_cont i j s ρ S z σ hs hρ]

theorem sigma_pow_mul_E (i j : ℕ) (θA θB ρ bb z σ : R)
    (hA : σ * θA = 1) (hB : σ * θB = bb) (hρ : σ * ρ = z) :
    σ ^ (min i j + 1) * E R i j θA θB ρ = frakE R i j ((i : R) + (j : R) * bb) z σ := by
  rw [← ES_eq_E i j θA θB ρ]
  refine sigma_pow_mul_ES i j _ ρ _ z σ ?_ hρ
  calc σ * (θA * (i : R) + θB * (j : R)) = (σ * θA) * (i : R) + (σ * θB) * (j : R) := by ring
    _ = (i : R) + (j : R) * bb := by rw [hA, hB]; ring

theorem frakE_eq_det_B_add_smul_C (i j : ℕ) (S z σ : R) :
    frakE R i j S z σ = (Bmat R i j S z + σ • Cmat R i j).det := rfl

theorem cont_of_b_zero (d c : ℕ → R) :
    ∀ r : ℕ, cont d (fun _ => 0) c r = ∏ t ∈ Finset.range r, d t := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [cont]
    | 1 => simp [cont]
    | (r + 2) =>
      rw [cont, ih (r + 1) (by omega), zero_mul, zero_mul, sub_zero]
      conv_rhs => rw [Finset.prod_range_succ]
      ring

theorem frakE_at_zero (i j : ℕ) (S z : R) :
    frakE R i j S z 0 = ∏ t ∈ Finset.range (min i j + 1), (S + z * (t : R)) := by
  rw [frakE_eq_cont]
  simp only [zero_mul, add_zero]
  exact cont_of_b_zero _ _ _

theorem frakE_at_zero_mul (i j : ℕ) (S z : R) :
    frakE R i j S z 0 = S * ∏ t ∈ Finset.Ico 1 (min i j + 1), (S + z * (t : R)) := by
  rw [frakE_at_zero, Finset.range_eq_Ico,
    Finset.prod_eq_prod_Ico_succ_bot (by omega : (0 : ℕ) < min i j + 1)]
  norm_num

theorem cont_map {S : Type*} [CommRing S] (f : R →+* S) (d b c : ℕ → R) :
    ∀ r : ℕ,
      f (cont d b c r) = cont (fun t => f (d t)) (fun t => f (b t)) (fun t => f (c t)) r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [cont]
    | 1 => simp [cont]
    | (r + 2) =>
      rw [cont, cont, map_sub, map_mul, map_mul, map_mul, ih (r + 1) (by omega), ih r (by omega)]

theorem frakE_map {S : Type*} [CommRing S] (f : R →+* S) (i j : ℕ) (S₀ z σ : R) :
    f (frakE R i j S₀ z σ) = frakE S i j (f S₀) (f z) (f σ) := by
  rw [frakE_eq_cont, frakE_eq_cont, cont_map f]
  congr 1
  · funext t
    simp only [bdiagE, ncoef, map_add, map_mul, map_natCast]
  · funext t
    simp only [bcoef, map_mul, map_natCast, map_neg, map_ofNat]
  · funext t
    simp only [ccoef, map_neg, map_mul, map_add, map_natCast, map_one]

variable (A : Type*) [CommRing A]

noncomputable def frakEP (i j : ℕ) (S σ : A) : A[X] :=
  frakE A[X] i j (Polynomial.C S) Polynomial.X (Polynomial.C σ)

variable {A}

theorem ncoef_polynomial (i j t : ℕ) :
    ncoef A[X] i j t = Polynomial.C (ncoef A i j t) := by
  simp [ncoef]

theorem bcoef_polynomial (i j t : ℕ) :
    bcoef A[X] i j t = Polynomial.C (bcoef A i j t) := by
  rw [bcoef, bcoef, map_mul, map_neg, map_ofNat, map_natCast]

theorem frakEP_map {B : Type*} [CommRing B] (f : A →+* B) (i j : ℕ) (S σ : A) :
    (frakEP A i j S σ).map f = frakEP B i j (f S) (f σ) := by
  rw [frakEP, frakEP, ← Polynomial.coe_mapRingHom, frakE_map (Polynomial.mapRingHom f)]
  simp

theorem frakEP_eval (i j : ℕ) (S σ z : A) :
    (frakEP A i j S σ).eval z = frakE A i j S z σ := by
  rw [frakEP, ← Polynomial.coe_evalRingHom, frakE_map (Polynomial.evalRingHom z)]
  simp

theorem natDegree_cont_le (d b c : ℕ → A[X]) (hd0 : (d 0).natDegree ≤ 0)
    (hd : ∀ t, (d t).natDegree ≤ 1) (hbc : ∀ t, (b t * c t).natDegree ≤ 1) :
    ∀ r : ℕ, (cont d b c r).natDegree ≤ r - 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [cont]
    | 1 => simpa [cont] using hd0
    | (r + 2) =>
      rw [cont]
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans (Polynomial.natDegree_mul_le) ?_
        have := ih (r + 1) (by omega)
        have h1 := hd (r + 1)
        omega
      · refine le_trans (Polynomial.natDegree_mul_le) ?_
        have := ih r (by omega)
        have h1 := hbc r
        omega

theorem natDegree_frakEP_le (i j : ℕ) (S σ : A) : (frakEP A i j S σ).natDegree ≤ min i j := by
  have hcc : ∀ t : ℕ, (ccoef A[X] (Polynomial.X : A[X]) t).natDegree ≤ 1 := by
    intro t
    rw [ccoef, Polynomial.natDegree_neg]
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have h2 : (((t : A[X]) + 1)).natDegree = 0 := by
      have hcast : ((t : A[X]) + 1) = ((t + 1 : ℕ) : A[X]) := by push_cast; ring
      rw [hcast, Polynomial.natDegree_natCast]
    have h1 : (Polynomial.X : A[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
    omega
  have hdiag : ∀ t : ℕ, (bdiagE A[X] (Polynomial.C S) Polynomial.X t
      + Polynomial.C σ * ncoef A[X] i j t).natDegree ≤ 1 := by
    intro t
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · rw [bdiagE]
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · rw [Polynomial.natDegree_C]; omega
      · refine le_trans (Polynomial.natDegree_mul_le) ?_
        rw [Polynomial.natDegree_natCast]
        have h1 : (Polynomial.X : A[X]).natDegree ≤ 1 := Polynomial.natDegree_X_le
        omega
    · rw [ncoef_polynomial]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_C, Polynomial.natDegree_C]
      omega
  have h := natDegree_cont_le (A := A)
    (fun t => bdiagE A[X] (Polynomial.C S) Polynomial.X t + Polynomial.C σ * ncoef A[X] i j t)
    (fun t => Polynomial.C σ * bcoef A[X] i j t) (ccoef A[X] Polynomial.X) ?_ hdiag ?_ (min i j + 1)
  · rw [frakEP, frakE_eq_cont]
    simpa using h
  · rw [bdiagE]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · rw [Polynomial.natDegree_C]
    · rw [ncoef_polynomial]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_C, Polynomial.natDegree_C]
  · intro t
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have h1 : (Polynomial.C σ * bcoef A[X] i j t).natDegree = 0 := by
      rw [bcoef_polynomial, ← Polynomial.C_mul, Polynomial.natDegree_C]
    have h2 := hcc t
    omega

end Rhone.Analysis.Rescale
