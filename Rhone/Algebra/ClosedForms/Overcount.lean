/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Defs

/-! # Why the naive product of `ρ = 0` diagonals over-counts -/

@[expose] public section

namespace Rhone.Algebra.ClosedForms

open LinearAlgebra.Recursion

def dval {R : Type*} [CommRing R] (θA θB : R) (i j k : ℕ) : R :=
  ((k * (k - 1) : ℕ) : R) + θA * i + θB * j

theorem diag_rho_zero {KA KB : ℕ} {R : Type*} [CommRing R] (θA θB : R) (ξ : Config KA KB) :
    diag θA θB 0 ξ = dval θA θB ξ.nA ξ.nB ξ.n := by
  simp only [diag, dval, zero_mul, add_zero]

def Proportional (i₁ j₁ k₁ i₂ j₂ k₂ : ℕ) : Prop :=
  ∃ c : ℚ, 0 < c ∧ ((k₁ * (k₁ - 1) : ℕ) : ℚ) = c * ((k₂ * (k₂ - 1) : ℕ) : ℚ)
    ∧ (i₁ : ℚ) = c * (i₂ : ℚ) ∧ (j₁ : ℚ) = c * (j₂ : ℚ)

theorem proportional_iff {i₁ j₁ k₁ i₂ j₂ k₂ : ℕ} (h1i : 2 ≤ i₁) (h2i : 2 ≤ i₂) :
    Proportional i₁ j₁ k₁ i₂ j₂ k₂ ↔
      (i₁ * j₂ = i₂ * j₁ ∧ k₁ * (k₁ - 1) * i₂ = k₂ * (k₂ - 1) * i₁) := by
  have hi1 : (0 : ℚ) < (i₁ : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le two_pos h1i
  have hi2 : (0 : ℚ) < (i₂ : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le two_pos h2i
  constructor
  · rintro ⟨c, hc, hk, hi, hj⟩
    constructor
    · have : ((i₁ * j₂ : ℕ) : ℚ) = ((i₂ * j₁ : ℕ) : ℚ) := by
        push_cast
        rw [hi, hj]
        ring
      exact_mod_cast this
    · have : ((k₁ * (k₁ - 1) * i₂ : ℕ) : ℚ) = ((k₂ * (k₂ - 1) * i₁ : ℕ) : ℚ) := by
        push_cast
        push_cast at hk hi
        rw [hk, hi]
        ring
      exact_mod_cast this
  · rintro ⟨hij, hk⟩
    refine ⟨(i₁ : ℚ) / (i₂ : ℚ), div_pos hi1 hi2, ?_, ?_, ?_⟩
    · have h : ((k₁ * (k₁ - 1) * i₂ : ℕ) : ℚ) = ((k₂ * (k₂ - 1) * i₁ : ℕ) : ℚ) := by
        exact_mod_cast hk
      push_cast at h ⊢
      field_simp
      linarith [h]
    · field_simp
    · have h : ((i₁ * j₂ : ℕ) : ℚ) = ((i₂ * j₁ : ℕ) : ℚ) := by exact_mod_cast hij
      push_cast at h ⊢
      field_simp
      linarith [h]

theorem dval_cross_mul {R : Type*} [CommRing R] (θA θB : R) {i₁ j₁ k₁ i₂ j₂ k₂ : ℕ}
    (hij : i₁ * j₂ = i₂ * j₁) (hk : k₁ * (k₁ - 1) * i₂ = k₂ * (k₂ - 1) * i₁) :
    (i₂ : R) * dval θA θB i₁ j₁ k₁ = (i₁ : R) * dval θA θB i₂ j₂ k₂ := by
  have e1 : ((k₁ * (k₁ - 1) * i₂ : ℕ) : R) = ((k₂ * (k₂ - 1) * i₁ : ℕ) : R) := by rw [hk]
  have e2 : ((i₁ * j₂ : ℕ) : R) = ((i₂ * j₁ : ℕ) : R) := by rw [hij]
  push_cast at e1 e2
  simp only [dval]
  push_cast
  linear_combination e1 - θB * e2

theorem mul_pred_injective {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (h : x * (x - 1) = y * (y - 1)) :
    x = y := by
  obtain ⟨a, rfl⟩ : ∃ a, x = a + 2 := ⟨x - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = b + 2 := ⟨y - 2, by omega⟩
  have ha : a + 2 - 1 = a + 1 := by omega
  have hb : b + 2 - 1 = b + 1 := by omega
  rw [ha, hb] at h
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exfalso; nlinarith
  · omega
  · exfalso; nlinarith

theorem eq_of_proportional_of_le {i₁ j₁ k₁ i₂ j₂ k₂ : ℕ} (h2i : 2 ≤ i₂) (h2k : 2 ≤ k₂)
    (h2k1 : 2 ≤ k₁) (hprop : Proportional i₁ j₁ k₁ i₂ j₂ k₂) (hi : i₁ = i₂) :
    j₁ = j₂ ∧ k₁ = k₂ := by
  obtain ⟨c, hc, hk, hii, hjj⟩ := hprop
  have hi2 : (0 : ℚ) < (i₂ : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le two_pos h2i
  have hc1 : c = 1 := by
    rw [hi] at hii
    rcases mul_left_eq_self₀.mp hii.symm with h | h
    · exact h
    · exact absurd h hi2.ne'
  subst hc1
  rw [one_mul] at hk hjj
  refine ⟨by exact_mod_cast hjj, mul_pred_injective h2k1 h2k (by exact_mod_cast hk)⟩

theorem coincidence_44_22 : Proportional 4 4 4 2 2 3 :=
  (proportional_iff (by norm_num) (by norm_num)).mpr ⟨by norm_num, by norm_num⟩

theorem dval_44_eq_two_mul {R : Type*} [CommRing R] (θA θB : R) :
    dval θA θB 4 4 4 = 2 * dval θA θB 2 2 3 := by
  simp only [dval]
  push_cast
  ring

theorem coincidence_55_33 : Proportional 5 5 5 3 3 4 :=
  (proportional_iff (by norm_num) (by norm_num)).mpr ⟨by norm_num, by norm_num⟩

theorem dval_55_eq_of_33 {R : Type*} [CommRing R] (θA θB : R) :
    3 * dval θA θB 5 5 5 = 5 * dval θA θB 3 3 4 := by
  simp only [dval]
  push_cast
  ring

end Rhone.Algebra.ClosedForms
