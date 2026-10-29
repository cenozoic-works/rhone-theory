/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.RecombinationExpansion.Continuant
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Order

/-! # Positivity of the continuants of the denominator matrix -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open LinearAlgebra.Tridiag LinearAlgebra.RecombinationExpansion

theorem nat_mul_pred (x : ℕ) : x * (x - 1) + x = x * x := by
  cases x with
  | zero => rfl
  | succ k => simp; ring

theorem nat_diag_split (I J t : ℕ) :
    I * (I - 1) + J * (J - 1) + t * (t - 1) + 2 * (t * I) + 2 * (t * J) + 2 * (I * J)
      = (I + J + t) * ((I + J + t) - 1) := by
  have h1 : I * (I - 1) + I = I * I := nat_mul_pred I
  have h2 : J * (J - 1) + J = J * J := nat_mul_pred J
  have h3 : t * (t - 1) + t = t * t := nat_mul_pred t
  have h4 : (I + J + t) * ((I + J + t) - 1) + (I + J + t) = (I + J + t) * (I + J + t) :=
    nat_mul_pred _
  have h5 : (I + J + t) * (I + J + t)
      = I * I + J * J + t * t + 2 * (t * I) + 2 * (t * J) + 2 * (I * J) := by ring
  omega

section Semiring

variable {S : Type*} [CommSemiring S]

def dA (i j : ℕ) (θA θB : S) (t : ℕ) : S :=
  (((i + j - t) * (i + j - t - 1) : ℕ) : S) + θA * i + θB * j

def dA' (i j : ℕ) (θA θB : S) (t : ℕ) : S :=
  (((i - t) * (i - t - 1) + (j - t) * (j - t - 1) + t * (t - 1)
      + 2 * (t * (i - t)) + 2 * (t * (j - t)) : ℕ) : S) + θA * i + θB * j

def hOff (S : Type*) [CommSemiring S] (i j t : ℕ) : S := ((2 * ((i - t) * (j - t)) : ℕ) : S)

theorem dA'_add_hOff (i j t : ℕ) (hi : t ≤ i) (hj : t ≤ j) (θA θB : S) :
    dA' i j θA θB t + hOff S i j t = dA i j θA θB t := by
  have hnat : (i - t) * (i - t - 1) + (j - t) * (j - t - 1) + t * (t - 1)
        + 2 * (t * (i - t)) + 2 * (t * (j - t)) + 2 * ((i - t) * (j - t))
      = (i + j - t) * (i + j - t - 1) := by
    have h := nat_diag_split (i - t) (j - t) t
    rwa [show (i - t) + (j - t) + t = i + j - t from by omega] at h
  have hcast : (((i - t) * (i - t - 1) + (j - t) * (j - t - 1) + t * (t - 1)
        + 2 * (t * (i - t)) + 2 * (t * (j - t)) : ℕ) : S) + ((2 * ((i - t) * (j - t)) : ℕ) : S)
      = (((i + j - t) * (i + j - t - 1) : ℕ) : S) := by
    rw [← Nat.cast_add, hnat]
  simp only [dA, dA', hOff]
  rw [← hcast]
  ring

def PH (i j : ℕ) (θA θB ρ : S) : ℕ → S × S
  | 0 => (dA i j θA θB 0, dA' i j θA θB 0)
  | (k + 1) =>
      (dA i j θA θB (k + 1) * (PH i j θA θB ρ k).1
          + ρ * ((k + 1 : ℕ) : S) * (PH i j θA θB ρ k).2,
       dA' i j θA θB (k + 1) * (PH i j θA θB ρ k).1
          + ρ * ((k + 1 : ℕ) : S) * (PH i j θA θB ρ k).2)

def QN (i j : ℕ) (θA θB ρ : S) (m : ℕ) : ℕ → S × S
  | 0 => (1, 1)
  | (u + 1) =>
      (dA' i j θA θB (m - u) * (QN i j θA θB ρ m u).1
            + hOff S i j (m - u) * (QN i j θA θB ρ m u).2
          + ρ * ((m - u : ℕ) : S) * (QN i j θA θB ρ m u).1,
       dA' i j θA θB (m - u) * (QN i j θA θB ρ m u).1
          + hOff S i j (m - u) * (QN i j θA θB ρ m u).2)

end Semiring

section Mem

variable {S : Type*} [CommSemiring S] (A : Subsemiring S)

theorem dA_mem (i j t : ℕ) {θA θB : S} (hA : θA ∈ A) (hB : θB ∈ A) :
    dA i j θA θB t ∈ A :=
  A.add_mem (A.add_mem (natCast_mem A _) (A.mul_mem hA (natCast_mem A i)))
    (A.mul_mem hB (natCast_mem A j))

theorem dA'_mem (i j t : ℕ) {θA θB : S} (hA : θA ∈ A) (hB : θB ∈ A) :
    dA' i j θA θB t ∈ A :=
  A.add_mem (A.add_mem (natCast_mem A _) (A.mul_mem hA (natCast_mem A i)))
    (A.mul_mem hB (natCast_mem A j))

theorem hOff_mem (i j t : ℕ) : hOff S i j t ∈ A := natCast_mem A _

theorem PH_mem (i j : ℕ) {θA θB ρ : S} (hA : θA ∈ A) (hB : θB ∈ A) (hρ : ρ ∈ A) :
    ∀ k : ℕ, (PH i j θA θB ρ k).1 ∈ A ∧ (PH i j θA θB ρ k).2 ∈ A := by
  intro k
  induction k with
  | zero => exact ⟨dA_mem A i j 0 hA hB, dA'_mem A i j 0 hA hB⟩
  | succ k ih =>
    exact ⟨A.add_mem (A.mul_mem (dA_mem A i j (k + 1) hA hB) ih.1)
        (A.mul_mem (A.mul_mem hρ (natCast_mem A _)) ih.2),
      A.add_mem (A.mul_mem (dA'_mem A i j (k + 1) hA hB) ih.1)
        (A.mul_mem (A.mul_mem hρ (natCast_mem A _)) ih.2)⟩

theorem QN_mem (i j m : ℕ) {θA θB ρ : S} (hA : θA ∈ A) (hB : θB ∈ A) (hρ : ρ ∈ A) :
    ∀ u : ℕ, (QN i j θA θB ρ m u).1 ∈ A ∧ (QN i j θA θB ρ m u).2 ∈ A := by
  intro u
  induction u with
  | zero => exact ⟨A.one_mem, A.one_mem⟩
  | succ u ih =>
    have hN : dA' i j θA θB (m - u) * (QN i j θA θB ρ m u).1
        + hOff S i j (m - u) * (QN i j θA θB ρ m u).2 ∈ A :=
      A.add_mem (A.mul_mem (dA'_mem A i j (m - u) hA hB) ih.1)
        (A.mul_mem (hOff_mem A i j (m - u)) ih.2)
    exact ⟨A.add_mem hN (A.mul_mem (A.mul_mem hρ (natCast_mem A _)) ih.1), hN⟩

end Mem

section Ring

variable {R : Type*} [CommRing R]

theorem dcoef_eq_dA (i j t : ℕ) (θA θB ρ : R) :
    dcoef R i j θA θB ρ t = dA i j θA θB t + ρ * (t : R) := rfl

theorem bcoef_mul_ccoef_eq (i j t : ℕ) (ρ : R) :
    bcoef R i j t * ccoef R ρ t = ρ * ((t + 1 : ℕ) : R) * hOff R i j t := by
  rw [bcoef_mul_ccoef]
  simp only [hOff]
  push_cast
  ring

theorem PH_eq_cont (i j : ℕ) (θA θB ρ : R) :
    ∀ k : ℕ, k ≤ min i j →
      (PH i j θA θB ρ k).1 = cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (k + 1)
      ∧ (PH i j θA θB ρ k).2
          = cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (k + 1)
            - hOff R i j k * cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) k := by
  intro k
  induction k with
  | zero =>
    intro _
    have hc1 : cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) 1
        = dcoef R i j θA θB ρ 0 := rfl
    have hc0 : cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) 0 = (1 : R) := rfl
    have hsplit := dA'_add_hOff i j 0 (Nat.zero_le i) (Nat.zero_le j) θA θB
    refine ⟨?_, ?_⟩
    · change dA i j θA θB 0 = _
      rw [hc1, dcoef_eq_dA]
      simp
    · change dA' i j θA θB 0 = _
      rw [hc1, hc0, dcoef_eq_dA]
      simp only [Nat.cast_zero, mul_zero, add_zero, mul_one]
      linear_combination hsplit
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hki : k + 1 ≤ i := by omega
    have hkj : k + 1 ≤ j := by omega
    have hsplit := dA'_add_hOff i j (k + 1) hki hkj θA θB
    have hrec : cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (k + 2)
        = dcoef R i j θA θB ρ (k + 1)
            * cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (k + 1)
          - bcoef R i j k * ccoef R ρ k
            * cont (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) k := rfl
    rw [bcoef_mul_ccoef_eq, dcoef_eq_dA] at hrec
    constructor
    · change dA i j θA θB (k + 1) * (PH i j θA θB ρ k).1
        + ρ * ((k + 1 : ℕ) : R) * (PH i j θA θB ρ k).2 = _
      rw [ih1, ih2, hrec]
      ring
    · change dA' i j θA θB (k + 1) * (PH i j θA θB ρ k).1
        + ρ * ((k + 1 : ℕ) : R) * (PH i j θA θB ρ k).2 = _
      rw [ih1, ih2, hrec, ← hsplit]
      ring

theorem QN_eq_Qc (i j m : ℕ) (hmi : m ≤ i) (hmj : m ≤ j) (θA θB ρ : R) :
    ∀ u : ℕ, u ≤ m + 1 →
      (QN i j θA θB ρ m u).1
          = Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (m + 1) (m + 1 - u)
      ∧ (QN i j θA θB ρ m u).2
          = Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (m + 1) (m + 1 - u)
            - ρ * ((m + 1 - u : ℕ) : R)
              * Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (m + 1) (m + 2 - u) := by
  intro u
  induction u with
  | zero =>
    intro _
    have h1 : m + 1 - 0 = m + 1 := by omega
    have h2 : m + 2 - 0 = m + 1 + 1 := by omega
    refine ⟨?_, ?_⟩
    · change (1 : R) = _
      rw [h1, Qc_self]
    · change (1 : R) = _
      rw [h1, h2, Qc_self, Qc_succ_self]
      ring
  | succ u ih =>
    intro hu
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hs : m + 1 - (u + 1) = m - u := by omega
    have hs1 : m + 1 - u = (m - u) + 1 := by omega
    have hs2 : m + 2 - u = (m - u) + 2 := by omega
    have hs2' : m + 2 - (u + 1) = (m - u) + 1 := by omega
    have hsi : m - u ≤ i := by omega
    have hsj : m - u ≤ j := by omega
    have hsplit := dA'_add_hOff i j (m - u) hsi hsj θA θB
    have hrec : Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (m + 1) (m - u)
        = dcoef R i j θA θB ρ (m - u)
            * Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (m + 1) ((m - u) + 1)
          - bcoef R i j (m - u) * ccoef R ρ (m - u)
            * Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (m + 1) ((m - u) + 2) :=
      Qc_rec _ _ _ (by omega)
    rw [bcoef_mul_ccoef_eq, dcoef_eq_dA] at hrec
    rw [hs1] at ih1
    rw [hs1, hs2] at ih2
    have hN : dA' i j θA θB (m - u) * (QN i j θA θB ρ m u).1
          + hOff R i j (m - u) * (QN i j θA θB ρ m u).2
        = Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (m + 1) (m - u)
          - ρ * ((m - u : ℕ) : R)
            * Qc (dcoef R i j θA θB ρ) (bcoef R i j) (ccoef R ρ) (m + 1) ((m - u) + 1) := by
      rw [ih1, ih2, hrec, ← hsplit]
      push_cast
      ring
    refine ⟨?_, ?_⟩
    · change dA' i j θA θB (m - u) * (QN i j θA θB ρ m u).1
          + hOff R i j (m - u) * (QN i j θA θB ρ m u).2
        + ρ * ((m - u : ℕ) : R) * (QN i j θA θB ρ m u).1 = _
      rw [hs, hN, ih1]
      ring
    · change dA' i j θA θB (m - u) * (QN i j θA θB ρ m u).1
          + hOff R i j (m - u) * (QN i j θA θB ρ m u).2 = _
      rw [hs, hs2', hN]

end Ring

end Rhone.Analysis.RecombinationExpansion
