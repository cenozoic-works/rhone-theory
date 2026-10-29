/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Tactic.Positivity

/-! # `E_{i,j} > 0` on the whole parameter domain, so no pole is nonnegative -/

@[expose] public section

namespace Rhone.LinearAlgebra.GaloisDegreeSeven

open Tridiag

theorem natCast_mul_pred_nonneg (a : ℕ) : (0 : ℤ) ≤ (a : ℤ) * ((a : ℤ) - 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · simp
  · have h1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast h
    nlinarith

theorem two_mul_le_nat (t a b : ℕ) : 2 * (a * b) ≤ (t + a + b) * (t + a + b - 1) := by
  rcases Nat.eq_zero_or_pos (t + a + b) with h | h
  · have ha : a = 0 := by omega
    simp [ha]
  · have h1 : 1 ≤ t + a + b := h
    zify [h1]
    have hT : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    have hA : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
    have hB : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
    have hA1 := natCast_mul_pred_nonneg a
    have hB1 := natCast_mul_pred_nonneg b
    have hT1 : (0 : ℤ) ≤ (t : ℤ) * (2 * ((a : ℤ) + (b : ℤ)) + (t : ℤ) - 1) := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp
      · have h1t : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
        nlinarith
    have key : ((t : ℤ) + a + b) * ((t : ℤ) + a + b - 1) - 2 * ((a : ℤ) * b)
        = (a : ℤ) * ((a : ℤ) - 1) + (b : ℤ) * ((b : ℤ) - 1)
          + (t : ℤ) * (2 * ((a : ℤ) + (b : ℤ)) + (t : ℤ) - 1) := by ring
    linarith

section Defs

variable (F : Type*) [CommRing F]

def upRate (i j t : ℕ) : F := 2 * (((i - t) * (j - t) : ℕ) : F)

def rowSum (i j : ℕ) (θA θB : F) (t : ℕ) : F :=
  (((i + j - t) * (i + j - t - 1) : ℕ) : F) + θA * i + θB * j - upRate F i j t

end Defs

section Ring

variable {F : Type*} [CommRing F]

theorem dcoef_eq_rowSum (i j : ℕ) (θA θB ρ : F) (t : ℕ) :
    dcoef F i j θA θB ρ t = rowSum F i j θA θB t + upRate F i j t + ρ * t := by
  simp only [dcoef, rowSum]
  ring

theorem bcoef_mul_ccoef_upRate (i j : ℕ) (ρ : F) (t : ℕ) :
    bcoef F i j t * ccoef F ρ t = ρ * ((t : F) + 1) * upRate F i j t := by
  rw [bcoef_mul_ccoef]
  simp only [upRate]
  ring

end Ring

section Order

variable {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]

theorem upRate_nonneg (i j t : ℕ) : (0 : F) ≤ upRate F i j t := by
  unfold upRate
  positivity

theorem rowSum_nonneg {i j t : ℕ} {θA θB : F} (hi : t ≤ i) (hj : t ≤ j)
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) : (0 : F) ≤ rowSum F i j θA θB t := by
  have hnat : 2 * ((i - t) * (j - t)) ≤ (i + j - t) * (i + j - t - 1) := by
    have h := two_mul_le_nat t (i - t) (j - t)
    rwa [show t + (i - t) + (j - t) = i + j - t from by omega] at h
  have hcast : upRate F i j t ≤ (((i + j - t) * (i + j - t - 1) : ℕ) : F) := by
    unfold upRate
    exact_mod_cast hnat
  have h1 : (0 : F) ≤ θA * i := mul_nonneg hA (Nat.cast_nonneg i)
  have h2 : (0 : F) ≤ θB * j := mul_nonneg hB (Nat.cast_nonneg j)
  unfold rowSum
  linarith

theorem upRate_pos_of_lt {i j t : ℕ} (h : t < min i j) : (0 : F) < upRate F i j t := by
  have h1 : 1 ≤ (i - t) * (j - t) :=
    mul_pos (by omega : 0 < i - t) (by omega : 0 < j - t)
  have hc : (1 : F) ≤ (((i - t) * (j - t) : ℕ) : F) := by exact_mod_cast h1
  unfold upRate
  linarith

theorem upRate_min (i j : ℕ) : upRate F i j (min i j) = 0 := by
  have h : (i - min i j) * (j - min i j) = 0 := by
    rcases le_total i j with hle | hle
    · rw [Nat.min_eq_left hle]; simp
    · rw [Nat.min_eq_right hle]; simp
  unfold upRate
  rw [h]
  simp

theorem rowSum_min_pos {i j : ℕ} {θA θB : F} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) : (0 : F) < rowSum F i j θA θB (min i j) := by
  set m := min i j with hm
  have hnat : 2 ≤ (i + j - m) * (i + j - m - 1) := by
    have h1 : 2 ≤ i + j - m := by omega
    have h2 : 1 ≤ i + j - m - 1 := by omega
    calc 2 = 2 * 1 := by norm_num
      _ ≤ (i + j - m) * (i + j - m - 1) := Nat.mul_le_mul h1 h2
  have hcast : (2 : F) ≤ (((i + j - m) * (i + j - m - 1) : ℕ) : F) := by exact_mod_cast hnat
  have h1 : (0 : F) ≤ θA * i := mul_nonneg hA (Nat.cast_nonneg i)
  have h2 : (0 : F) ≤ θB * j := mul_nonneg hB (Nat.cast_nonneg j)
  have h0 : upRate F i j m = 0 := upRate_min i j
  unfold rowSum
  rw [h0]
  linarith

theorem cont_invariant {i j : ℕ} {θA θB ρ : F}
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    ∀ t : ℕ, t ≤ min i j →
      0 < cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) t ∧
        (upRate F i j t + rowSum F i j θA θB t) *
            cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) t
          ≤ cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (t + 1) := by
  intro t
  induction t with
  | zero =>
    intro _
    have h0 : cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) 0 = 1 := rfl
    have h1 : cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) 1
        = dcoef F i j θA θB ρ 0 := rfl
    refine ⟨by rw [h0]; norm_num, ?_⟩
    rw [h0, h1, dcoef_eq_rowSum]
    simp only [Nat.cast_zero, mul_zero, add_zero, mul_one]
    linarith
  | succ n ih =>
    intro hn
    have hn' : n ≤ min i j := by omega
    obtain ⟨hpos, hstep⟩ := ih hn'
    have hup : (0 : F) < upRate F i j n := upRate_pos_of_lt (by omega)
    have hrow : (0 : F) ≤ rowSum F i j θA θB n :=
      rowSum_nonneg (by omega) (by omega) hA hB
    have hposn : 0 < cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (n + 1) := by
      have : (0 : F) < (upRate F i j n + rowSum F i j θA θB n) *
          cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) n :=
        mul_pos (by linarith) hpos
      linarith
    refine ⟨hposn, ?_⟩
    have hrec : cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (n + 2)
        = dcoef F i j θA θB ρ (n + 1) *
            cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (n + 1)
          - bcoef F i j n * ccoef F ρ n *
            cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) n := rfl
    rw [hrec, dcoef_eq_rowSum, bcoef_mul_ccoef_upRate]
    have hcarry : upRate F i j n * cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) n
        ≤ cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (n + 1) := by
      have : (0 : F) ≤ rowSum F i j θA θB n *
          cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) n :=
        mul_nonneg hrow hpos.le
      linarith [hstep]
    have hcoef : (0 : F) ≤ ρ * ((n : F) + 1) := by positivity
    push_cast
    have hnn : (0 : F) ≤ ρ * ((n : F) + 1) *
        (cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (n + 1)
          - upRate F i j n * cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) n) :=
      mul_nonneg hcoef (by linarith)
    nlinarith [hnn]

theorem E_pos {i j : ℕ} {θA θB ρ : F} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) : 0 < E F i j θA θB ρ := by
  obtain ⟨hpos, hstep⟩ := cont_invariant hA hB hρ (min i j) le_rfl
  have hup : upRate F i j (min i j) = 0 := upRate_min i j
  have hrow : (0 : F) < rowSum F i j θA θB (min i j) := rowSum_min_pos hi hj hA hB
  rw [E_eq_cont]
  have : (0 : F) < (upRate F i j (min i j) + rowSum F i j θA θB (min i j)) *
      cont (dcoef F i j θA θB ρ) (bcoef F i j) (ccoef F ρ) (min i j) :=
    mul_pos (by rw [hup]; linarith) hpos
  linarith

theorem E_ne_zero {i j : ℕ} {θA θB ρ : F} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) : E F i j θA θB ρ ≠ 0 :=
  (E_pos hi hj hA hB hρ).ne'

end Order

end Rhone.LinearAlgebra.GaloisDegreeSeven
