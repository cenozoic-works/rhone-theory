/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.RecombinationExpansion.Usmani
public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # The scalar tridiagonals `T_k^{(i,j)}` -/

@[expose] public section

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset Matrix Tridiag RecombinationExpansion

variable {F : Type*} [Field F]

def sig (i j k : ℕ) : ℕ := min (i - 2 * k) (j - k)

def dK (θA θB ρ : F) (i j k s : ℕ) : F := dcoef F i j θA θB ρ (k + s)

def bK (F : Type*) [Field F] (i j k s : ℕ) : F :=
  -2 * (((j - k - s) * (s + 1) * (i - 2 * k - s) : ℕ) : F)

def cK (ρ : F) (_s : ℕ) : F := -ρ

def TK (θA θB ρ : F) (i j k : ℕ) : Matrix (Fin (sig i j k + 1)) (Fin (sig i j k + 1)) F :=
  trid (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1)

def detK (θA θB ρ : F) (i j k : ℕ) : F :=
  cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1)

theorem det_TK (θA θB ρ : F) (i j k : ℕ) : (TK θA θB ρ i j k).det = detK θA θB ρ i j k :=
  det_trid_eq_cont _ _ _ _

def GK (θA θB ρ : F) (i j k s s' : ℕ) : F :=
  usmaniEntry (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1) s s' / detK θA θB ρ i j k

theorem trid_mulVec_apply (d b c : ℕ → F) {n : ℕ} (w : ℕ → F) (hw : w n = 0) {I : ℕ}
    (hI : I < n) :
    (trid d b c n *ᵥ fun m : Fin n => w m) ⟨I, hI⟩
      = (if I = 0 then 0 else c (I - 1) * w (I - 1)) + d I * w I + b I * w (I + 1) := by
  have h1 : (trid d b c n *ᵥ fun m : Fin n => w m) ⟨I, hI⟩
      = ∑ m : Fin n, tridEntry d b c I (m : ℕ) * w (m : ℕ) := rfl
  rw [h1, trid_row_range d b c w hw hI]
  match I with
  | 0 => rw [trid_row_zero, ite_eq_left rfl, zero_add]
  | I' + 1 =>
    rw [show I' + 1 + 2 = I' + 3 from by omega, trid_row_succ, ite_eq_right (by omega),
      Nat.add_sub_cancel]

theorem bK_eq {i j k s : ℕ} (hk : 2 * k ≤ i) (hs : s ≤ i - 2 * k) :
    bK F i j k s
      = -(2 * ((j - (k + s) : ℕ) : F) * ((s : F) + 1) * ((i : F) - 2 * (k : F) - (s : F))) := by
  rw [bK, Nat.sub_sub, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hs, Nat.cast_sub hk]
  push_cast
  ring

theorem bK_sig (i j k : ℕ) : bK F i j k (sig i j k) = 0 := by
  have : (j - k - sig i j k) * (sig i j k + 1) * (i - 2 * k - sig i j k) = 0 := by
    rcases min_choice (i - 2 * k) (j - k) with h | h
    · rw [sig, h, Nat.sub_self, mul_zero]
    · rw [sig, h, Nat.sub_self, zero_mul, zero_mul]
  rw [bK, this, Nat.cast_zero, mul_zero]

theorem TK_GK {θA θB ρ : F} {i j k : ℕ} (hk : 2 * k ≤ i)
    (hdet : detK θA θB ρ i j k ≠ 0) {s s' : ℕ} (hs : s ≤ sig i j k) (hs' : s' ≤ sig i j k) :
    dcoef F i j θA θB ρ (k + s) * GK θA θB ρ i j k s s'
        - (if s = 0 then 0 else ρ * GK θA θB ρ i j k (s - 1) s')
        - (2 * ((j - (k + s) : ℕ) : F) * ((s : F) + 1) * ((i : F) - 2 * (k : F) - (s : F)))
            * GK θA θB ρ i j k (s + 1) s'
      = if s = s' then 1 else 0 := by
  have hI : s < sig i j k + 1 := by omega
  have hJ : s' < sig i j k + 1 := by omega
  have h := congrFun (congrFun (trid_mul_usmani (dK θA θB ρ i j k) (bK F i j k) (cK ρ)
    (sig i j k + 1)) ⟨s, hI⟩) ⟨s', hJ⟩
  have h1 : (trid (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1)
      * usmani (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1)) ⟨s, hI⟩ ⟨s', hJ⟩
      = (trid (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1) *ᵥ fun m : Fin _ =>
          usmaniEntry (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (sig i j k + 1) m s') ⟨s, hI⟩ := rfl
  rw [h1, trid_mulVec_apply _ _ _ (fun m => usmaniEntry (dK θA θB ρ i j k) (bK F i j k) (cK ρ)
    (sig i j k + 1) m s') (usmaniEntry_top _ _ _ hJ) hI, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, bK_eq hk (le_trans hs (min_le_left _ _))] at h
  simp only [GK]
  simp only [dK, cK, Fin.mk.injEq] at h
  rw [← detK] at h
  split_ifs at h ⊢ <;> field_simp <;> linear_combination h

theorem two_mul_mul_le {a b N : ℕ} (h : a + b ≤ N) : 2 * (a * b) ≤ N * (N - 1) := by
  have h1 : (a + b) * (a + b - 1) ≤ N * (N - 1) := Nat.mul_le_mul h (by omega)
  have h2 : 2 * (a * b) ≤ (a + b) * (a + b - 1) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [show a' + 1 + b - 1 = a' + b from by omega]
      nlinarith [Nat.le_mul_self b, Nat.zero_le (a' * a'), Nat.zero_le a']
  exact le_trans h2 h1

section Ordered

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem detK_pos {θA θB ρ : F} {i j : ℕ} (hρ : 0 ≤ ρ) (hδ : 0 < θA * i + θB * j)
    (k : ℕ) : 0 < detK θA θB ρ i j k := by
  set w : ℕ → F := fun n => (((j - k - n) * (i - 2 * k - n) : ℕ) : F) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => Nat.cast_nonneg _
  have hg : ∀ n, n ≤ sig i j k → 2 * w n + (θA * i + θB * j) ≤ dK θA θB ρ i j k n - ρ * n := by
    intro n hn
    have hn1 : n ≤ i - 2 * k := le_trans hn (min_le_left _ _)
    have hn2 : n ≤ j - k := le_trans hn (min_le_right _ _)
    have h1 : 2 * ((j - k - n) * (i - 2 * k - n))
        ≤ (i + j - (k + n)) * (i + j - (k + n) - 1) := two_mul_mul_le (by omega)
    have h2 : (2 : F) * w n ≤ (((i + j - (k + n)) * (i + j - (k + n) - 1) : ℕ) : F) := by
      have := (Nat.cast_le (α := F)).mpr h1
      rw [hw]
      push_cast at this ⊢
      exact this
    have h3 : (0 : F) ≤ ρ * k := mul_nonneg hρ (Nat.cast_nonneg k)
    rw [dK, dcoef]
    push_cast at h2 ⊢
    linarith
  have hbc : ∀ n, bK F i j k n * cK ρ n = ρ * ((n : F) + 1) * (2 * w n) := by
    intro n
    rw [bK, cK, hw]
    push_cast
    ring
  have key : ∀ n, n ≤ sig i j k →
      0 < cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) n ∧
        (dK θA θB ρ i j k n - ρ * n) * cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) n
          ≤ cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) 0 = 1 := rfl
      have h1 : cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (0 + 1) = dK θA θB ρ i j k 0 := rfl
      rw [h0, h1]
      exact ⟨one_pos, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨hpos, hstep⟩ := ih (by omega)
      have hgn := hg n (by omega)
      have hgpos : 0 < dK θA θB ρ i j k n - ρ * n := by linarith [hw0 n]
      have hpos' : 0 < cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (n + 1) :=
        lt_of_lt_of_le (mul_pos hgpos hpos) hstep
      refine ⟨hpos', ?_⟩
      have hrec : cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (n + 1 + 1)
          = dK θA θB ρ i j k (n + 1) * cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (n + 1)
            - bK F i j k n * cK ρ n * cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) n := rfl
      have h2w : 2 * w n * cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) n
          ≤ cont (dK θA θB ρ i j k) (bK F i j k) (cK ρ) (n + 1) := by
        refine le_trans (mul_le_mul_of_nonneg_right ?_ hpos.le) hstep
        linarith
      have hρn : (0 : F) ≤ ρ * ((n : F) + 1) :=
        mul_nonneg hρ (by positivity)
      have := mul_le_mul_of_nonneg_left h2w hρn
      rw [hrec, hbc]
      push_cast
      linarith
  obtain ⟨hpos, hstep⟩ := key (sig i j k) le_rfl
  have hgn := hg (sig i j k) le_rfl
  have hgpos : 0 < dK θA θB ρ i j k (sig i j k) - ρ * (sig i j k : ℕ) := by
    linarith [hw0 (sig i j k)]
  exact lt_of_lt_of_le (mul_pos hgpos hpos) hstep

theorem detK_ne_zero {θA θB ρ : F} {i j : ℕ} (hρ : 0 ≤ ρ) (hδ : 0 < θA * i + θB * j)
    (k : ℕ) : detK θA θB ρ i j k ≠ 0 :=
  (detK_pos hρ hδ k).ne'

end Ordered

end Rhone.LinearAlgebra.BooleanLatticeInverse
