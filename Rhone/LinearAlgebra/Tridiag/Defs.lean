/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Block

/-! # The tridiagonal within-block generator `T^{(i,j)}` and `E_{i,j} = det T^{(i,j)}` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Tridiag

open Matrix

variable (R : Type*) [CommRing R]

def dcoef (i j : ℕ) (θA θB ρ : R) (t : ℕ) : R :=
  (((i + j - t) * (i + j - t - 1) : ℕ) : R) + θA * i + θB * j + ρ * t

def bcoef (i j : ℕ) (t : ℕ) : R := -2 * (((i - t) * (j - t) : ℕ) : R)

def ccoef (ρ : R) (t : ℕ) : R := -(ρ * ((t : R) + 1))

def T (i j : ℕ) (θA θB ρ : R) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1)

def E (i j : ℕ) (θA θB ρ : R) : R := (T R i j θA θB ρ).det

variable {R}

@[simp]
theorem T_apply (i j : ℕ) (θA θB ρ : R) (p q : Fin (min i j + 1)) :
    T R i j θA θB ρ p q = tridEntry (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) p q := rfl

theorem T_diag (i j : ℕ) (θA θB ρ : R) (p : Fin (min i j + 1)) :
    T R i j θA θB ρ p p =
      (((i + j - (p : ℕ)) * (i + j - (p : ℕ) - 1) : ℕ) : R) + θA * i + θB * j + ρ * (p : ℕ) :=
  tridEntry_of_eq _ _ _ rfl

theorem T_super (i j : ℕ) (θA θB ρ : R) (p q : Fin (min i j + 1)) (h : (q : ℕ) = (p : ℕ) + 1) :
    T R i j θA θB ρ p q = -2 * (((i - (p : ℕ)) * (j - (p : ℕ)) : ℕ) : R) :=
  tridEntry_of_succ _ _ _ h

theorem T_sub (i j : ℕ) (θA θB ρ : R) (p q : Fin (min i j + 1)) (h : (p : ℕ) = (q : ℕ) + 1) :
    T R i j θA θB ρ p q = -(ρ * (((q : ℕ) : R) + 1)) :=
  tridEntry_of_pred _ _ _ h

theorem T_zero (i j : ℕ) (θA θB ρ : R) (p q : Fin (min i j + 1))
    (h : (q : ℕ) + 1 < (p : ℕ) ∨ (p : ℕ) + 1 < (q : ℕ)) : T R i j θA θB ρ p q = 0 := by
  rcases h with h | h
  · exact tridEntry_of_gt _ _ _ h
  · exact tridEntry_of_lt _ _ _ h

theorem T_map {S : Type*} [CommRing S] (f : R →+* S) (i j : ℕ) (θA θB ρ : R) :
    (T R i j θA θB ρ).map f = T S i j (f θA) (f θB) (f ρ) := by
  ext p q
  simp only [Matrix.map_apply, T_apply, tridEntry, dcoef, bcoef, ccoef, apply_ite f]
  split_ifs <;> push_cast <;> simp [map_ofNat]

theorem E_map {S : Type*} [CommRing S] (f : R →+* S) (i j : ℕ) (θA θB ρ : R) :
    f (E R i j θA θB ρ) = E S i j (f θA) (f θB) (f ρ) := by
  rw [E, E, ← T_map f, RingHom.map_det]
  rfl

theorem T_two_two_generic (θA θB ρ : R) :
    T R 2 2 θA θB ρ =
      !![12 + θA * 2 + θB * 2, -8, 0;
         -ρ, 6 + θA * 2 + θB * 2 + ρ, -2;
         0, -(ρ * 2), 2 + θA * 2 + θB * 2 + ρ * 2] := by
  refine Matrix.ext fun p q => ?_
  fin_cases p <;> fin_cases q <;> norm_num [T, trid, tridEntry, dcoef, bcoef, ccoef]

theorem bcoef_mul_ccoef (i j : ℕ) (ρ : R) (t : ℕ) :
    bcoef R i j t * ccoef R ρ t = 2 * ρ * ((t : R) + 1) * (((i - t) * (j - t) : ℕ) : R) := by
  simp only [bcoef, ccoef]
  ring

theorem E_eq_cont (i j : ℕ) (θA θB ρ : R) :
    E R i j θA θB ρ = cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1) := by
  rw [E, T, det_trid_eq_cont]

theorem eq_zero_of_mulVec_eq_zero [NoZeroDivisors R] (i j : ℕ) (θA θB ρ : R)
    (hE : E R i j θA θB ρ ≠ 0) {Φ : Fin (min i j + 1) → R} (hΦ : T R i j θA θB ρ *ᵥ Φ = 0) :
    Φ = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero hE hΦ

theorem isUpperTriangular_T_rho_zero (i j : ℕ) (θA θB : R) :
    (T R i j θA θB 0).IsUpperTriangular := by
  intro p q h
  have hq : (q : ℕ) < (p : ℕ) := h
  rw [T_apply, tridEntry, ite_eq_right (by omega), ite_eq_right (by omega)]
  split_ifs with h3
  · simp [ccoef]
  · rfl

theorem E_rho_zero (i j : ℕ) (θA θB : R) :
    E R i j θA θB 0 = ∏ t : Fin (min i j + 1), dcoef R i j θA θB 0 (t : ℕ) := by
  rw [E, Matrix.det_of_isUpperTriangular (isUpperTriangular_T_rho_zero i j θA θB)]
  exact Finset.prod_congr rfl fun t _ => tridEntry_of_eq _ _ _ rfl

variable (R)

def Tcoal (i j : ℕ) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (fun t => (((i + j - t) * (i + j - t - 1) : ℕ) : R)) (bcoef R i j) 0 (min i j + 1)

def TmutA (i j : ℕ) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (fun _ => (i : R)) 0 0 (min i j + 1)

def TmutB (i j : ℕ) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (fun _ => (j : R)) 0 0 (min i j + 1)

def Trec (i j : ℕ) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (fun t => (t : R)) 0 (fun t => -((t : R) + 1)) (min i j + 1)

variable {R}

theorem T_eq_classes (i j : ℕ) (θA θB ρ : R) :
    T R i j θA θB ρ = Tcoal R i j + θA • TmutA R i j + θB • TmutB R i j + ρ • Trec R i j := by
  ext p q
  simp only [T_apply, Matrix.add_apply, Matrix.smul_apply, Tcoal, TmutA, TmutB, Trec, trid_apply,
    tridEntry, dcoef, bcoef, ccoef, Pi.zero_apply, smul_eq_mul]
  split_ifs <;> ring

end Rhone.LinearAlgebra.Tridiag
