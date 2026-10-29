/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Rhone.Analysis.RecombinationExpansion.Continuant
public import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Mutation-scaled tridiagonal system, its determinant `E`, and the Usmani inverse -/

@[expose] public section

namespace Rhone.Analysis.DenominatorEquation

open Matrix LinearAlgebra.Tridiag RecombinationExpansion LinearAlgebra.RecombinationExpansion

variable (R : Type*) [CommRing R]

def dcoefS (i j : ℕ) (s ρ : R) (t : ℕ) : R :=
  (((i + j - t) * (i + j - t - 1) : ℕ) : R) + s + ρ * t

def TS (i j : ℕ) (s ρ : R) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  trid (dcoefS R i j s ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1)

def ES (i j : ℕ) (s ρ : R) : R := (TS R i j s ρ).det

variable {R}

theorem dcoefS_eq_dcoef (i j : ℕ) (θA θB ρ : R) (t : ℕ) :
    dcoefS R i j (θA * (i : R) + θB * (j : R)) ρ t = dcoef R i j θA θB ρ t := by
  simp only [dcoefS, dcoef]
  ring

theorem TS_eq_T (i j : ℕ) (θA θB ρ : R) :
    TS R i j (θA * (i : R) + θB * (j : R)) ρ = T R i j θA θB ρ := by
  rw [TS, T]
  congr 1
  funext t
  exact dcoefS_eq_dcoef i j θA θB ρ t

theorem ES_eq_E (i j : ℕ) (θA θB ρ : R) :
    ES R i j (θA * (i : R) + θB * (j : R)) ρ = E R i j θA θB ρ := by
  rw [ES, E, TS_eq_T]

theorem E_indep_of_theta (i j : ℕ) (θA θB θA' θB' ρ : R)
    (h : θA * (i : R) + θB * (j : R) = θA' * (i : R) + θB' * (j : R)) :
    E R i j θA θB ρ = E R i j θA' θB' ρ := by
  rw [← ES_eq_E i j θA θB ρ, ← ES_eq_E i j θA' θB' ρ, h]

theorem ES_eq_cont (i j : ℕ) (s ρ : R) :
    ES R i j s ρ = cont (dcoefS R i j s ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1) := by
  rw [ES, TS, det_trid_eq_cont]

variable (R)

def Delta (i j : ℕ) (θA θB ρ : R) (a : ℕ) : R :=
  cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) a

def DeltaP (i j : ℕ) (θA θB ρ : R) (k : ℕ) : R :=
  Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1) k

variable {R}

@[simp]
theorem Delta_zero (i j : ℕ) (θA θB ρ : R) : Delta R i j θA θB ρ 0 = 1 := rfl

@[simp]
theorem Delta_one (i j : ℕ) (θA θB ρ : R) :
    Delta R i j θA θB ρ 1 = dcoef R i j θA θB ρ 0 := rfl

theorem Delta_top (i j : ℕ) (θA θB ρ : R) :
    Delta R i j θA θB ρ (min i j + 1) = E R i j θA θB ρ := (E_eq_cont i j θA θB ρ).symm

theorem Delta_rec (i j : ℕ) (θA θB ρ : R) (a : ℕ) :
    Delta R i j θA θB ρ (a + 2)
      = dcoef R i j θA θB ρ (a + 1) * Delta R i j θA θB ρ (a + 1)
        - bcoef R i j a * ccoef R ρ a * Delta R i j θA θB ρ a := rfl

@[simp]
theorem DeltaP_top (i j : ℕ) (θA θB ρ : R) : DeltaP R i j θA θB ρ (min i j + 1) = 1 :=
  Qc_self _ _ _ _

@[simp]
theorem DeltaP_top_succ (i j : ℕ) (θA θB ρ : R) : DeltaP R i j θA θB ρ (min i j + 2) = 0 :=
  Qc_succ_self _ _ _ _

theorem DeltaP_rec (i j : ℕ) (θA θB ρ : R) {k : ℕ} (h : k < min i j + 1) :
    DeltaP R i j θA θB ρ k
      = dcoef R i j θA θB ρ k * DeltaP R i j θA θB ρ (k + 1)
        - bcoef R i j k * ccoef R ρ k * DeltaP R i j θA θB ρ (k + 2) :=
  Qc_rec _ _ _ h

theorem cut (i j : ℕ) (θA θB ρ : R) {a : ℕ} (h : a < min i j + 1) :
    Delta R i j θA θB ρ (a + 1) * DeltaP R i j θA θB ρ (a + 1)
      - bcoef R i j a * ccoef R ρ a * Delta R i j θA θB ρ a
          * DeltaP R i j θA θB ρ (a + 2)
      = E R i j θA θB ρ := by
  rw [Delta, Delta, DeltaP, DeltaP, E_eq_cont]
  exact cont_mul_Qc' _ _ _ h

theorem bc_eq (i j : ℕ) (ρ : R) (a : ℕ) :
    bcoef R i j a * ccoef R ρ a = 2 * ρ * ((a : R) + 1) * (((i - a) * (j - a) : ℕ) : R) :=
  bcoef_mul_ccoef i j ρ a

variable (R)

def U (i j : ℕ) (θA θB ρ : R) : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R :=
  usmani (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1)

def ell (i j : ℕ) (θA θB ρ : R) (s : ℕ) : R :=
  usmaniEntry (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1) 0 s

variable {R}

@[simp]
theorem U_apply (i j : ℕ) (θA θB ρ : R) (t t' : Fin (min i j + 1)) :
    U R i j θA θB ρ t t'
      = usmaniEntry (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1)
          (t : ℕ) (t' : ℕ) := rfl

theorem U_zero_apply (i j : ℕ) (θA θB ρ : R) (t' : Fin (min i j + 1)) :
    U R i j θA θB ρ 0 t' = ell R i j θA θB ρ (t' : ℕ) := by
  rw [U_apply, ell]
  rfl

theorem T_mul_U (i j : ℕ) (θA θB ρ : R) :
    T R i j θA θB ρ * U R i j θA θB ρ
      = (E R i j θA θB ρ) • (1 : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R) :=
  T_mul_usmani i j θA θB ρ

theorem U_mul_T (i j : ℕ) (θA θB ρ : R) :
    U R i j θA θB ρ * T R i j θA θB ρ
      = (E R i j θA θB ρ) • (1 : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R) := by
  rw [U, T_eq_trid, usmani_mul_trid, E_eq_cont]

theorem prod_eq_descFactorial (i j s : ℕ) :
    (∏ u ∈ Finset.range s, ((i - u) * (j - u))) = i.descFactorial s * j.descFactorial s := by
  rw [Finset.prod_mul_distrib, Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]

theorem ell_eq (i j : ℕ) (θA θB ρ : R) (s : ℕ) :
    ell R i j θA θB ρ s
      = 2 ^ s * ((i.descFactorial s * j.descFactorial s : ℕ) : R)
          * DeltaP R i j θA θB ρ (s + 1) := by
  rw [ell, usmaniEntry_T_of_le i j θA θB ρ (Nat.zero_le s), DeltaP]
  have h0 : cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) 0 = 1 := rfl
  rw [h0, mul_one, Nat.sub_zero]
  congr 2
  rw [← Nat.cast_prod, ← prod_eq_descFactorial]
  exact congrArg _ (Finset.prod_congr (by rw [Finset.range_eq_Ico]) fun _ _ => rfl)

theorem adj_last_col (i j : ℕ) (θA θB ρ : R) {t : ℕ} (ht : t ≤ min i j) :
    usmaniEntry (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1) t (min i j)
      = 2 ^ (min i j - t) * (∏ u ∈ Finset.Ico t (min i j), (((i - u) * (j - u) : ℕ) : R))
          * Delta R i j θA θB ρ t := by
  rw [usmaniEntry_T_of_le i j θA θB ρ ht, Qc_self, mul_one, Delta]

theorem adj_zero_last (i j : ℕ) (θA θB ρ : R) :
    ell R i j θA θB ρ (min i j)
      = 2 ^ (min i j)
        * ((i.descFactorial (min i j) * j.descFactorial (min i j) : ℕ) : R) := by
  rw [ell_eq, DeltaP_top, mul_one]

end Rhone.Analysis.DenominatorEquation
