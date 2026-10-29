/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.RecombinationExpansion.Usmani
public import Rhone.LinearAlgebra.Tridiag.Defs

/-! # Continuants and the explicit inverse of the block generator `T^{(i,j)}` -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open Matrix LinearAlgebra.Tridiag

variable {R : Type*} [CommRing R]

theorem cont_of_offdiag_zero (d b c : ℕ → R) (hbc : ∀ s, b s * c s = 0) (k : ℕ) :
    cont d b c k = ∏ u ∈ Finset.range k, d u := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [cont]
    | 1 => simp [cont]
    | (r + 2) =>
      change d (r + 1) * cont d b c (r + 1) - b r * c r * cont d b c r = _
      rw [ih (r + 1) (by omega), hbc r, zero_mul, sub_zero]
      conv_rhs => rw [Finset.prod_range_succ]
      ring

theorem cont_rho_zero (i j : ℕ) (θA θB : R) (k : ℕ) :
    cont (dcoef R i j θA θB 0) (bcoef R i j) (ccoef R 0) k
      = ∏ u ∈ Finset.range k, dcoef R i j θA θB 0 u := by
  refine cont_of_offdiag_zero _ _ _ (fun s => ?_) k
  simp [ccoef]

theorem card_Ico_cast (t t' : ℕ) : (Finset.Ico t t').card = t' - t := Nat.card_Ico t t'

theorem sign_bcoef_run (i j : ℕ) {t t' : ℕ} (h : t ≤ t') :
    (-1 : R) ^ (t + t') * LinearAlgebra.RecombinationExpansion.runProd (bcoef R i j) t t'
      = 2 ^ (t' - t) * ∏ s ∈ Finset.Ico t t', (((i - s) * (j - s) : ℕ) : R) := by
  have hprod : LinearAlgebra.RecombinationExpansion.runProd (bcoef R i j) t t'
      = (-2 : R) ^ (t' - t) * ∏ s ∈ Finset.Ico t t', (((i - s) * (j - s) : ℕ) : R) := by
    rw [LinearAlgebra.RecombinationExpansion.runProd, show (fun s => bcoef R i j s) = fun s =>
        (-2 : R) * (((i - s) * (j - s) : ℕ) : R)
      from rfl, Finset.prod_mul_distrib, Finset.prod_const, card_Ico_cast]
  have hsign : (-1 : R) ^ (t + t') * (-2 : R) ^ (t' - t) = 2 ^ (t' - t) := by
    rw [show (-2 : R) = (-1 : R) * 2 from by ring, mul_pow, ← mul_assoc, ← pow_add,
      show t + t' + (t' - t) = 2 * t' from by omega, pow_mul]
    norm_num
  rw [hprod, ← mul_assoc, hsign]

theorem sign_ccoef_run (ρ : R) {t t' : ℕ} (h : t' ≤ t) :
    (-1 : R) ^ (t + t') * LinearAlgebra.RecombinationExpansion.runProd (ccoef R ρ) t' t
      = ρ ^ (t - t') * ∏ s ∈ Finset.Ico t' t, ((s : R) + 1) := by
  have hprod : LinearAlgebra.RecombinationExpansion.runProd (ccoef R ρ) t' t
      = (-1 : R) ^ (t - t') * (ρ ^ (t - t') * ∏ s ∈ Finset.Ico t' t, ((s : R) + 1)) := by
    have hcg : ∀ s ∈ Finset.Ico t' t, ccoef R ρ s = (-1 : R) * (ρ * ((s : R) + 1)) := by
      intro s _
      simp only [ccoef]
      ring
    rw [LinearAlgebra.RecombinationExpansion.runProd, Finset.prod_congr rfl hcg,
        Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, card_Ico_cast]
  have hsign : (-1 : R) ^ (t + t') * (-1 : R) ^ (t - t') = 1 := by
    rw [← pow_add, show t + t' + (t - t') = 2 * t from by omega, pow_mul]
    norm_num
  rw [hprod, ← mul_assoc, hsign, one_mul]

theorem T_eq_trid (i j : ℕ) (θA θB ρ : R) :
    T R i j θA θB ρ = trid (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (min i j + 1) := rfl

theorem usmaniEntry_T_of_le (i j : ℕ) (θA θB ρ : R) {t t' : ℕ} (h : t ≤ t') :
    LinearAlgebra.RecombinationExpansion.usmaniEntry (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ)
        (min i j + 1) t t'
      = 2 ^ (t' - t) * (∏ s ∈ Finset.Ico t t', (((i - s) * (j - s) : ℕ) : R))
          * cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) t
          * LinearAlgebra.RecombinationExpansion.Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ)
              (min i j + 1) (t' + 1) := by
  rw [LinearAlgebra.RecombinationExpansion.usmaniEntry_of_le _ _ _ _ h, mul_assoc
      ((-1 : R) ^ (t + t')), ← mul_assoc,
    sign_bcoef_run i j h]

theorem usmaniEntry_T_of_ge (i j : ℕ) (θA θB ρ : R) {t t' : ℕ} (h : t' ≤ t) :
    LinearAlgebra.RecombinationExpansion.usmaniEntry (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ)
        (min i j + 1) t t'
      = ρ ^ (t - t') * (∏ s ∈ Finset.Ico t' t, ((s : R) + 1))
          * cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) t'
          * LinearAlgebra.RecombinationExpansion.Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ)
              (min i j + 1) (t + 1) := by
  rw [LinearAlgebra.RecombinationExpansion.usmaniEntry_of_ge _ _ _ _ h, mul_assoc
      ((-1 : R) ^ (t + t')), ← mul_assoc,
    sign_ccoef_run ρ h]

theorem prod_sub_mul_factorial_aux {i t : ℕ} : ∀ k : ℕ, t + k ≤ i →
    (∏ s ∈ Finset.Ico t (t + k), (i - s)) * Nat.factorial (i - (t + k))
      = Nat.factorial (i - t) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ r ih =>
    intro h2
    rw [show t + (r + 1) = (t + r) + 1 from by omega,
      Finset.prod_Ico_succ_top (by omega : t ≤ t + r), mul_assoc,
      show (i - (t + r)) * Nat.factorial (i - (t + r + 1)) = Nat.factorial (i - (t + r)) from by
        rw [show i - (t + r + 1) = (i - (t + r)) - 1 from by omega]
        exact Nat.mul_factorial_pred (by omega)]
    exact ih (by omega)

theorem prod_sub_mul_factorial {i t t' : ℕ} (h : t ≤ t') (h2 : t' ≤ i) :
    (∏ s ∈ Finset.Ico t t', (i - s)) * Nat.factorial (i - t') = Nat.factorial (i - t) := by
  obtain ⟨k, rfl⟩ : ∃ k, t' = t + k := ⟨t' - t, by omega⟩
  exact prod_sub_mul_factorial_aux k h2

theorem prod_succ_mul_factorial_aux {t' : ℕ} : ∀ k : ℕ,
    (∏ s ∈ Finset.Ico t' (t' + k), (s + 1)) * Nat.factorial t' = Nat.factorial (t' + k) := by
  intro k
  induction k with
  | zero => simp
  | succ r ih =>
    rw [show t' + (r + 1) = (t' + r) + 1 from by omega,
      Finset.prod_Ico_succ_top (by omega : t' ≤ t' + r), mul_right_comm, ih,
      Nat.factorial_succ]
    ring

theorem prod_succ_mul_factorial {t' t : ℕ} (h : t' ≤ t) :
    (∏ s ∈ Finset.Ico t' t, (s + 1)) * Nat.factorial t' = Nat.factorial t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = t' + k := ⟨t - t', by omega⟩
  exact prod_succ_mul_factorial_aux k

section Field

variable {F : Type*} [Field F]

theorem inv_T_apply_of_le (i j : ℕ) (θA θB ρ : F) (hE : E F i j θA θB ρ ≠ 0)
    (t t' : Fin (min i j + 1)) (h : (t : ℕ) ≤ (t' : ℕ)) :
    (T F i j θA θB ρ)⁻¹ t t'
      = 2 ^ ((t' : ℕ) - (t : ℕ))
          * (∏ s ∈ Finset.Ico (t : ℕ) (t' : ℕ), (((i - s) * (j - s) : ℕ) : F))
          * cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (t : ℕ)
          * LinearAlgebra.RecombinationExpansion.Qc (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ)
              (min i j + 1) ((t' : ℕ) + 1)
        / E F i j θA θB ρ := by
  have hc : cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (min i j + 1) ≠ 0 := by
    rw [← E_eq_cont]; exact hE
  rw [T_eq_trid, LinearAlgebra.RecombinationExpansion.inv_trid _ _ _ _ hc, Matrix.smul_apply,
      LinearAlgebra.RecombinationExpansion.usmani_apply,
    usmaniEntry_T_of_le i j θA θB ρ h, smul_eq_mul, div_eq_inv_mul, E_eq_cont]

theorem inv_T_apply_of_ge (i j : ℕ) (θA θB ρ : F) (hE : E F i j θA θB ρ ≠ 0)
    (t t' : Fin (min i j + 1)) (h : (t' : ℕ) ≤ (t : ℕ)) :
    (T F i j θA θB ρ)⁻¹ t t'
      = ρ ^ ((t : ℕ) - (t' : ℕ))
          * (∏ s ∈ Finset.Ico (t' : ℕ) (t : ℕ), ((s : F) + 1))
          * cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (t' : ℕ)
          * LinearAlgebra.RecombinationExpansion.Qc (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ)
              (min i j + 1) ((t : ℕ) + 1)
        / E F i j θA θB ρ := by
  have hc : cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (min i j + 1) ≠ 0 := by
    rw [← E_eq_cont]; exact hE
  rw [T_eq_trid, LinearAlgebra.RecombinationExpansion.inv_trid _ _ _ _ hc, Matrix.smul_apply,
      LinearAlgebra.RecombinationExpansion.usmani_apply,
    usmaniEntry_T_of_ge i j θA θB ρ h, smul_eq_mul, div_eq_inv_mul, E_eq_cont]

theorem inv_T_zero_zero (i j : ℕ) (θA θB ρ : F) (hE : E F i j θA θB ρ ≠ 0) :
    (T F i j θA θB ρ)⁻¹ 0 0
      = LinearAlgebra.RecombinationExpansion.Qc (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ)
          (min i j + 1) 1
        / E F i j θA θB ρ := by
  have h := inv_T_apply_of_le i j θA θB ρ hE 0 0 (le_refl _)
  rw [h]
  simp only [Fin.val_zero, Nat.sub_self, pow_zero, Finset.Ico_self, Finset.prod_empty,
    one_mul, mul_one, zero_add]
  rw [show cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) 0 = (1 : F) from rfl, one_mul]

theorem T_mul_usmani (i j : ℕ) (θA θB ρ : R) :
    T R i j θA θB ρ * LinearAlgebra.RecombinationExpansion.usmani (dcoef R i j θA θB ρ)
        (bcoef R i j) (ccoef R ρ) (min i j + 1)
      = (E R i j θA θB ρ) • (1 : Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R) := by
  rw [T_eq_trid, LinearAlgebra.RecombinationExpansion.trid_mul_usmani, E_eq_cont]

end Field

end Rhone.Analysis.RecombinationExpansion
