/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.LinearCombination

/-! # The `ρ`-degree of `E_{i,j}` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Tridiag

open Polynomial

variable {F : Type*} [CommRing F]

theorem natDegree_linear_le (α β : F) : (C α + C β * X).natDegree ≤ 1 := by
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · simp
  · exact le_trans (natDegree_C_mul_le _ _) natDegree_X_le

theorem coeff_linear_mul (α β : F) (p : Polynomial F) (n : ℕ) :
    ((C α + C β * X) * p).coeff (n + 1) = α * p.coeff (n + 1) + β * p.coeff n := by
  rw [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_mul]

theorem degree_and_coeff_of_tridFrom (d b c : ℕ → Polynomial F) (α β γ : ℕ → F)
    (hd : ∀ s, d s = C (α s) + C (β s) * X) (hbc : ∀ s, b s * c s = C (γ s) * X) :
    ∀ r s : ℕ, (tridFrom d b c s r).det.natDegree ≤ r ∧
      (tridFrom d b c s r).det.coeff r = ∏ u ∈ Finset.range r, β (s + u) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => intro s; simp
    | 1 =>
      intro s
      rw [det_tridFrom_one, hd s]
      refine ⟨natDegree_linear_le _ _, ?_⟩
      rw [coeff_add, coeff_C_mul, coeff_C, coeff_X_one]
      simp
    | (k + 2) =>
      intro s
      obtain ⟨hdeg1, hcoeff1⟩ := ih (k + 1) (by omega) (s + 1)
      obtain ⟨hdeg2, hcoeff2⟩ := ih k (by omega) (s + 2)
      rw [det_tridFrom_add_two, hd s, hbc s]
      set Q1 := (tridFrom d b c (s + 1) (k + 1)).det with hQ1
      set Q2 := (tridFrom d b c (s + 2) k).det with hQ2
      constructor
      · refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
        · exact le_trans (natDegree_mul_le)
            (by have := natDegree_linear_le (α s) (β s); omega)
        · refine le_trans (natDegree_mul_le) ?_
          have h : (C (γ s) * X).natDegree ≤ 1 :=
            le_trans (natDegree_C_mul_le _ _) natDegree_X_le
          omega
      · have hz1 : Q1.coeff (k + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        have hz2 : Q2.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        have hγ : (C (γ s) * X * Q2).coeff (k + 2) = γ s * Q2.coeff (k + 1) := by
          rw [mul_assoc, coeff_C_mul, coeff_X_mul]
        rw [coeff_sub, coeff_linear_mul, hγ, hz1, hz2, hcoeff1]
        rw [Finset.prod_range_succ' (fun u => β (s + u)) (k + 1)]
        have : ∀ u : ℕ, β (s + 1 + u) = β (s + (u + 1)) := by
          intro u; congr 1; omega
        simp only [this, Nat.add_zero]
        ring1

variable (i j : ℕ) (a b : F)

def alphaT (t : ℕ) : F := (((i + j - t) * (i + j - t - 1) : ℕ) : F) + a * i + b * j

def gammaT (t : ℕ) : F := 2 * (((i - t) * (j - t) : ℕ) : F) * ((t : F) + 1)

theorem dcoef_poly (t : ℕ) :
    dcoef (Polynomial F) i j (C a) (C b) X t = C (alphaT i j a b t) + C ((t : F)) * X := by
  simp only [dcoef, alphaT, map_add, map_mul, map_natCast]
  ring1

theorem bcoef_mul_ccoef_poly (t : ℕ) :
    bcoef (Polynomial F) i j t * ccoef (Polynomial F) X t = C (gammaT i j t) * X := by
  simp only [bcoef, ccoef, gammaT, map_add, map_mul, map_one, map_ofNat, map_natCast]
  ring1

def kappaT : F := (i : F) * ((i : F) - 1 + a) + (j : F) * ((j : F) - 1 + b)

theorem prod_one_add (m : ℕ) :
    (∏ u ∈ Finset.range m, ((1 + u : ℕ) : F)) = (Nat.factorial m : F) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring1

theorem prod_two_add (m : ℕ) :
    (∏ u ∈ Finset.range m, ((2 + u : ℕ) : F)) = (Nat.factorial (m + 1) : F) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ (k + 1)]
    push_cast
    ring1

theorem natCast_mul_pred (n : ℕ) : ((n * (n - 1) : ℕ) : F) = (n : F) * ((n : F) - 1) := by
  cases n with
  | zero => simp
  | succ k => push_cast [Nat.add_sub_cancel]; ring

theorem alphaT_zero_sub :
    alphaT i j a b 0 - 2 * ((i * j : ℕ) : F) = kappaT i j a b := by
  simp only [alphaT, kappaT, Nat.sub_zero, natCast_mul_pred]
  push_cast
  ring1

theorem E_eq_det_tridFrom :
    E (Polynomial F) i j (C a) (C b) X
      = (tridFrom (dcoef (Polynomial F) i j (C a) (C b) X) (bcoef (Polynomial F) i j)
          (ccoef (Polynomial F) X) 0 (min i j + 1)).det := by
  rw [E, T, tridFrom_zero]

theorem degree_and_coeff_T (r s : ℕ) :
    (tridFrom (dcoef (Polynomial F) i j (C a) (C b) X) (bcoef (Polynomial F) i j)
        (ccoef (Polynomial F) X) s r).det.natDegree ≤ r ∧
      (tridFrom (dcoef (Polynomial F) i j (C a) (C b) X) (bcoef (Polynomial F) i j)
        (ccoef (Polynomial F) X) s r).det.coeff r
          = ∏ u ∈ Finset.range r, ((s + u : ℕ) : F) :=
  degree_and_coeff_of_tridFrom _ _ _ (alphaT i j a b) (fun t => (t : F)) (gammaT i j)
    (dcoef_poly i j a b) (bcoef_mul_ccoef_poly i j) r s

theorem natDegree_E_le : (E (Polynomial F) i j (C a) (C b) X).natDegree ≤ min i j := by
  obtain ⟨hdeg, hcoeff⟩ := degree_and_coeff_T i j a b (min i j + 1) 0
  rw [← E_eq_det_tridFrom] at hdeg hcoeff
  have hzero : (E (Polynomial F) i j (C a) (C b) X).coeff (min i j + 1) = 0 := by
    rw [hcoeff, Finset.prod_range_succ' (fun u => ((0 + u : ℕ) : F)) (min i j)]
    simp
  rcases Nat.lt_or_ge (E (Polynomial F) i j (C a) (C b) X).natDegree (min i j + 1) with h | h
  · omega
  · have heq : (E (Polynomial F) i j (C a) (C b) X).natDegree = min i j + 1 :=
      le_antisymm hdeg h
    have hlead : (E (Polynomial F) i j (C a) (C b) X).leadingCoeff = 0 := by
      rw [leadingCoeff, heq]; exact hzero
    rw [leadingCoeff_eq_zero] at hlead
    rw [hlead]
    simp

theorem coeff_leading_block (r : ℕ) :
    (tridFrom (dcoef (Polynomial F) i j (C a) (C b) X) (bcoef (Polynomial F) i j)
        (ccoef (Polynomial F) X) 0 (r + 2)).det.coeff (r + 1)
      = (Nat.factorial (r + 1) : F) * kappaT i j a b := by
  obtain ⟨_, hc1⟩ := degree_and_coeff_T i j a b (r + 1) 1
  obtain ⟨_, hc2⟩ := degree_and_coeff_T i j a b r 2
  rw [prod_one_add] at hc1
  rw [prod_two_add] at hc2
  rw [det_tridFrom_add_two, dcoef_poly, bcoef_mul_ccoef_poly, coeff_sub, coeff_linear_mul,
    mul_assoc, coeff_C_mul, coeff_X_mul, hc1, hc2]
  simp only [gammaT, Nat.sub_zero, Nat.cast_zero, zero_add, mul_one, zero_mul, add_zero]
  linear_combination (Nat.factorial (r + 1) : F) * alphaT_zero_sub i j a b

theorem coeff_E_min :
    (E (Polynomial F) i j (C a) (C b) X).coeff (min i j)
      = (Nat.factorial (min i j) : F) * kappaT i j a b := by
  rw [E_eq_det_tridFrom]
  rcases Nat.eq_zero_or_pos (min i j) with hm | hm
  · have hij : i = 0 ∨ j = 0 := by omega
    have hij0 : ((i * j : ℕ) : F) = 0 := by
      rcases hij with h | h <;> simp [h]
    rw [hm, Nat.zero_add, det_tridFrom_one, dcoef_poly, coeff_add, coeff_C_mul, coeff_X_zero,
      coeff_C]
    norm_num
    rw [← alphaT_zero_sub i j a b, hij0]
    ring1
  · obtain ⟨k, hk⟩ : ∃ k, min i j = k + 1 := ⟨min i j - 1, by omega⟩
    rw [hk, show k + 1 + 1 = k + 2 from rfl]
    exact coeff_leading_block i j a b k

theorem natDegree_E (h : (Nat.factorial (min i j) : F) * kappaT i j a b ≠ 0) :
    (E (Polynomial F) i j (C a) (C b) X).natDegree = min i j := by
  refine le_antisymm (natDegree_E_le i j a b) (le_natDegree_of_ne_zero ?_)
  rw [coeff_E_min]
  exact h

theorem natDegree_E_of_charZero [NoZeroDivisors F] [CharZero F] (hκ : kappaT i j a b ≠ 0) :
    (E (Polynomial F) i j (C a) (C b) X).natDegree = min i j :=
  natDegree_E i j a b (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) hκ)

theorem leadingCoeff_E (h : (Nat.factorial (min i j) : F) * kappaT i j a b ≠ 0) :
    (E (Polynomial F) i j (C a) (C b) X).leadingCoeff
      = (Nat.factorial (min i j) : F) * kappaT i j a b := by
  rw [leadingCoeff, natDegree_E i j a b h, coeff_E_min]

theorem E_ne_zero (h : (Nat.factorial (min i j) : F) * kappaT i j a b ≠ 0) :
    E (Polynomial F) i j (C a) (C b) X ≠ 0 := by
  intro h0
  apply h
  rw [← coeff_E_min i j a b, h0, coeff_zero]

end Rhone.LinearAlgebra.Tridiag
