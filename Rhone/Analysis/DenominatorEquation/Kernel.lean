/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Basic

/-! # One-dimensional, non-degenerate kernel of `T^{(i,j)}` at a root of `E_{i,j}` -/

@[expose] public section

namespace Rhone.Analysis.DenominatorEquation

open Matrix LinearAlgebra.Tridiag RecombinationExpansion LinearAlgebra.RecombinationExpansion

variable {K : Type*} [Field K] [CharZero K]
variable (i j : ℕ) (θA θB ρ : K)

theorem ccoef_ne_zero (hρ : ρ ≠ 0) (u : ℕ) : ccoef K ρ u ≠ 0 := by
  rw [ccoef, neg_ne_zero]
  refine mul_ne_zero hρ ?_
  have : ((u : K) + 1) = ((u + 1 : ℕ) : K) := by push_cast; ring
  rw [this]
  exact Nat.cast_ne_zero.mpr (by omega)

theorem bcoef_ne_zero {u : ℕ} (hu : u < min i j) : bcoef K i j u ≠ 0 := by
  rw [bcoef]
  refine mul_ne_zero (by norm_num) ?_
  exact Nat.cast_ne_zero.mpr (by
    have h1 : u < i := lt_of_lt_of_le hu (min_le_left i j)
    have h2 : u < j := lt_of_lt_of_le hu (min_le_right i j)
    exact Nat.mul_ne_zero (by omega) (by omega))

theorem bc_ne_zero (hρ : ρ ≠ 0) {u : ℕ} (hu : u < min i j) :
    bcoef K i j u * ccoef K ρ u ≠ 0 :=
  mul_ne_zero (bcoef_ne_zero i j hu) (ccoef_ne_zero ρ hρ u)

omit [CharZero K] in
theorem root_ne_zero (h0 : ∏ t : Fin (min i j + 1), dcoef K i j θA θB 0 (t : ℕ) ≠ 0)
    (hE : E K i j θA θB ρ = 0) : ρ ≠ 0 := by
  intro hρ
  rw [hρ, E_rho_zero] at hE
  exact h0 hE

theorem DeltaP_not_consecutive (hρ : ρ ≠ 0) :
    ∀ d k : ℕ, k + d = min i j + 1 →
      ¬(DeltaP K i j θA θB ρ k = 0 ∧ DeltaP K i j θA θB ρ (k + 1) = 0) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d with
    | 0 =>
      intro k hk hcon
      rw [show k = min i j + 1 from by omega, DeltaP_top] at hcon
      exact one_ne_zero hcon.1
    | 1 =>
      intro k hk hcon
      rw [show k + 1 = min i j + 1 from by omega, DeltaP_top] at hcon
      exact one_ne_zero hcon.2
    | (d + 2) =>
      intro k hk hcon
      have hkm : k < min i j := by omega
      have hrec := DeltaP_rec (R := K) i j θA θB ρ (k := k) (by omega)
      rw [hcon.1, hcon.2, mul_zero, zero_sub] at hrec
      have hrec' : bcoef K i j k * ccoef K ρ k * DeltaP K i j θA θB ρ (k + 2) = 0 :=
        neg_eq_zero.mp hrec.symm
      have h2 : DeltaP K i j θA θB ρ (k + 2) = 0 :=
        (mul_eq_zero.mp hrec').resolve_left (bc_ne_zero i j ρ hρ hkm)
      exact ih (d + 1) (by omega) (k + 1) (by omega) ⟨hcon.2, h2⟩

theorem DeltaP_ne_zero (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 →
      DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    {s : ℕ} (hs : s ≤ min i j) : DeltaP K i j θA θB ρ (s + 1) ≠ 0 := by
  intro hzero
  rcases Nat.lt_or_ge s (min i j) with hsm | hsm
  · have h2 : DeltaP K i j θA θB ρ (s + 2) ≠ 0 := by
      intro h2
      exact DeltaP_not_consecutive i j θA θB ρ hρ (min i j - s) (s + 1) (by omega)
        ⟨hzero, h2⟩
    have hcut := cut (R := K) i j θA θB ρ (a := s) (by omega)
    rw [hE, hzero, mul_zero, zero_sub, neg_eq_zero] at hcut
    have hbc := bc_ne_zero i j ρ hρ hsm
    have h := (mul_eq_zero.mp hcut).resolve_right h2
    exact hcop s hsm ((mul_eq_zero.mp h).resolve_left hbc) hzero
  · have : s = min i j := by omega
    rw [this, DeltaP_top] at hzero
    exact one_ne_zero hzero

theorem Delta_ne_zero (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 →
      DeltaP K i j θA θB ρ (s + 1) ≠ 0) :
    ∀ t : ℕ, t ≤ min i j → Delta K i j θA θB ρ t ≠ 0 := by
  intro t
  induction t with
  | zero => intro _; rw [Delta_zero]; exact one_ne_zero
  | succ t ih =>
    intro ht hzero
    have htm : t < min i j := by omega
    have hcut := cut (R := K) i j θA θB ρ (a := t) (by omega)
    rw [hE, hzero, zero_mul, zero_sub, neg_eq_zero] at hcut
    have hP : DeltaP K i j θA θB ρ (t + 2) ≠ 0 :=
      DeltaP_ne_zero i j θA θB ρ hρ hE hcop (s := t + 1) (by omega)
    have hbc := bc_ne_zero i j ρ hρ htm
    have hd : Delta K i j θA θB ρ t = 0 := by
      have h := (mul_eq_zero.mp hcut).resolve_right hP
      exact (mul_eq_zero.mp h).resolve_left hbc
    exact ih (by omega) hd

theorem ell_ne_zero (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (hcop : ∀ s, s < min i j → Delta K i j θA θB ρ s = 0 →
      DeltaP K i j θA θB ρ (s + 1) ≠ 0)
    {s : ℕ} (hs : s ≤ min i j) : ell K i j θA θB ρ s ≠ 0 := by
  rw [ell_eq]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_)
    (DeltaP_ne_zero i j θA θB ρ hρ hE hcop hs)
  refine Nat.cast_ne_zero.mpr (Nat.mul_ne_zero ?_ ?_) <;>
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt] <;> omega

section Kernel

variable {i j θA θB ρ}

private def extd {n : ℕ} (v : Fin n → K) : ℕ → K := fun k => if h : k < n then v ⟨k, h⟩ else 0

omit [CharZero K] in
private theorem extd_coe {n : ℕ} (v : Fin n → K) (k : Fin n) : extd v (k : ℕ) = v k := by
  rw [extd, dite_eq_left k.isLt]

omit [CharZero K] in
private theorem extd_top {n : ℕ} (v : Fin n → K) : extd v n = 0 := by
  rw [extd, dite_eq_right (by omega)]

omit [CharZero K] in
private theorem vecMul_row (v : Fin (min i j + 1) → K)
    (hv : v ᵥ* T K i j θA θB ρ = 0) (s : Fin (min i j + 1)) :
    (∑ k ∈ Finset.range ((s : ℕ) + 2),
      tridEntry (dcoef K i j θA θB ρ) (ccoef K ρ) (bcoef K i j) (s : ℕ) k * extd v k) = 0 := by
  have h : (∑ k : Fin (min i j + 1),
      tridEntry (dcoef K i j θA θB ρ) (ccoef K ρ) (bcoef K i j) (s : ℕ) (k : ℕ)
        * extd v (k : ℕ)) = 0 := by
    have h0 : (v ᵥ* T K i j θA θB ρ) s = 0 := by rw [hv]; rfl
    rw [Matrix.vecMul, dotProduct] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [extd_coe, T_apply, tridEntry_swap]
    ring
  rw [← h]
  exact (trid_row_range (dcoef K i j θA θB ρ) (ccoef K ρ) (bcoef K i j) (extd v)
    (extd_top v) s.isLt).symm

theorem left_ker_eq_zero_of_head (hρ : ρ ≠ 0) (v : Fin (min i j + 1) → K)
    (hv : v ᵥ* T K i j θA θB ρ = 0) (h0 : v 0 = 0) : v = 0 := by
  have key : ∀ s : ℕ, s ≤ min i j → extd v s = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      match s with
      | 0 =>
        intro _
        rw [show (0 : ℕ) = ((0 : Fin (min i j + 1)) : ℕ) from rfl, extd_coe, h0]
      | 1 =>
        intro h1
        have hrow := vecMul_row v hv ⟨0, by omega⟩
        rw [show ((⟨0, by omega⟩ : Fin (min i j + 1)) : ℕ) = 0 from rfl] at hrow
        rw [trid_row_zero, ih 0 (by omega) (by omega), mul_zero, zero_add] at hrow
        exact (mul_eq_zero.mp hrow).resolve_left (ccoef_ne_zero ρ hρ 0)
      | (s + 2) =>
        intro hs
        have hrow := vecMul_row v hv ⟨s + 1, by omega⟩
        rw [show ((⟨s + 1, by omega⟩ : Fin (min i j + 1)) : ℕ) = s + 1 from rfl,
          show s + 1 + 2 = s + 3 from by omega, trid_row_succ,
          ih s (by omega) (by omega), ih (s + 1) (by omega) (by omega),
          mul_zero, mul_zero, zero_add, zero_add] at hrow
        exact (mul_eq_zero.mp hrow).resolve_left (ccoef_ne_zero ρ hρ (s + 1))
  funext t
  rw [← extd_coe v t]
  exact key (t : ℕ) (by have := t.isLt; omega)

theorem left_ker_ext (hρ : ρ ≠ 0) (v w : Fin (min i j + 1) → K)
    (hv : v ᵥ* T K i j θA θB ρ = 0) (hw : w ᵥ* T K i j θA θB ρ = 0) (h0 : v 0 = w 0) :
    v = w := by
  have hsub : (v - w) ᵥ* T K i j θA θB ρ = 0 := by
    rw [Matrix.sub_vecMul, hv, hw, sub_zero]
  have := left_ker_eq_zero_of_head hρ (v - w) hsub (by simp [h0])
  have h := congrFun this
  funext t
  have := h t
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

omit [CharZero K] in
theorem row_U_vecMul (hE : E K i j θA θB ρ = 0) (t : Fin (min i j + 1)) :
    (fun k => U K i j θA θB ρ t k) ᵥ* T K i j θA θB ρ = 0 := by
  funext s
  have h := congrFun (congrFun (U_mul_T (R := K) i j θA θB ρ) t) s
  rw [Matrix.mul_apply] at h
  rw [Matrix.vecMul, dotProduct]
  rw [h, hE]
  simp

theorem rank_one_congr (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (t s : Fin (min i j + 1)) :
    U K i j θA θB ρ 0 0 * U K i j θA θB ρ t s
      = U K i j θA θB ρ t 0 * U K i j θA θB ρ 0 s := by
  have hker : (U K i j θA θB ρ 0 0 • (fun k => U K i j θA θB ρ t k)
      - U K i j θA θB ρ t 0 • (fun k => U K i j θA θB ρ 0 k)) ᵥ* T K i j θA θB ρ = 0 := by
    rw [Matrix.sub_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, row_U_vecMul hE t,
      row_U_vecMul hE 0, smul_zero, smul_zero, sub_zero]
  have h0 : (U K i j θA θB ρ 0 0 • (fun k => U K i j θA θB ρ t k)
      - U K i j θA θB ρ t 0 • (fun k => U K i j θA θB ρ 0 k)) 0 = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have := congrFun (left_ker_eq_zero_of_head hρ _ hker h0) s
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem minor_two_two (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (h00 : U K i j θA θB ρ 0 0 ≠ 0) (t s : Fin (min i j + 1)) :
    U K i j θA θB ρ t s * U K i j θA θB ρ 0 (Fin.last (min i j))
      = U K i j θA θB ρ t (Fin.last (min i j)) * U K i j θA θB ρ 0 s := by
  have h1 := rank_one_congr hρ hE t s
  have h2 := rank_one_congr hρ hE t (Fin.last (min i j))
  have h : U K i j θA θB ρ 0 0
      * (U K i j θA θB ρ t s * U K i j θA θB ρ 0 (Fin.last (min i j))
        - U K i j θA θB ρ t (Fin.last (min i j)) * U K i j θA θB ρ 0 s) = 0 := by
    have e1 : U K i j θA θB ρ 0 0 * U K i j θA θB ρ t s
        = U K i j θA θB ρ t 0 * U K i j θA θB ρ 0 s := h1
    have e2 : U K i j θA θB ρ 0 0 * U K i j θA θB ρ t (Fin.last (min i j))
        = U K i j θA θB ρ t 0 * U K i j θA θB ρ 0 (Fin.last (min i j)) := h2
    have : U K i j θA θB ρ 0 0
        * (U K i j θA θB ρ t s * U K i j θA θB ρ 0 (Fin.last (min i j)))
        - U K i j θA θB ρ 0 0
          * (U K i j θA θB ρ t (Fin.last (min i j)) * U K i j θA θB ρ 0 s) = 0 := by
      rw [← mul_assoc, e1, ← mul_assoc, e2]
      ring
    linear_combination this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h00)

theorem left_ker_eq_smul_ell (hρ : ρ ≠ 0) (hE : E K i j θA θB ρ = 0)
    (h00 : U K i j θA θB ρ 0 0 ≠ 0) (v : Fin (min i j + 1) → K)
    (hv : v ᵥ* T K i j θA θB ρ = 0) :
    v = (v 0 / U K i j θA θB ρ 0 0) • (fun k => U K i j θA θB ρ 0 k) := by
  refine left_ker_ext hρ v _ hv ?_ ?_
  · rw [Matrix.smul_vecMul, row_U_vecMul hE 0, smul_zero]
  · simp only [Pi.smul_apply, smul_eq_mul]
    field_simp

end Kernel

end Rhone.Analysis.DenominatorEquation
