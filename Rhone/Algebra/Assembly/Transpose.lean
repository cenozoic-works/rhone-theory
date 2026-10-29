/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.RhoDegree

/-! # At `θ_A = θ_B` the transposed blocks coincide -/

@[expose] public section

namespace Rhone.Algebra.Assembly

open LinearAlgebra.Tridiag Polynomial

variable {R : Type*} [CommRing R]

theorem dcoef_transpose (i j : ℕ) (θ ρ : R) : dcoef R i j θ θ ρ = dcoef R j i θ θ ρ := by
  funext t
  simp only [dcoef, Nat.add_comm i j]
  ring

theorem bcoef_transpose (i j : ℕ) : bcoef R i j = bcoef R j i := by
  funext t
  simp only [bcoef, Nat.mul_comm]

theorem E_transpose (i j : ℕ) (θ ρ : R) : E R i j θ θ ρ = E R j i θ θ ρ := by
  rw [E_eq_cont, E_eq_cont, dcoef_transpose, bcoef_transpose, Nat.min_comm]

variable {F : Type*} [Field F]

theorem not_isCoprime_E_transpose [CharZero F] (i j : ℕ) (θ : F) (hm : 1 ≤ min i j)
    (hκ : kappaT i j θ θ ≠ 0) :
    ¬ IsCoprime (E F[X] i j (C θ) (C θ) X) (E F[X] j i (C θ) (C θ) X) := by
  rw [E_transpose (R := F[X]) j i (C θ) X]
  intro h
  have hunit : IsUnit (E F[X] i j (C θ) (C θ) X) := isCoprime_self.mp h
  have hdeg : (E F[X] i j (C θ) (C θ) X).natDegree = min i j :=
    natDegree_E_of_charZero i j θ θ hκ
  have := Polynomial.natDegree_eq_zero_of_isUnit hunit
  omega

theorem kappaT_ne_zero_of_pos [LinearOrder F] [IsStrictOrderedRing F] {i j : ℕ} {θ : F}
    (hi : 1 ≤ i) (hθ : 0 < θ) : kappaT i j θ θ ≠ 0 := by
  have h1 : (0 : F) < (i : F) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hi
  have h2 : (0 : F) ≤ (i : F) - 1 := by
    have : ((1 : ℕ) : F) ≤ (i : F) := by exact_mod_cast hi
    simpa using this
  have h3 : (0 : F) ≤ (j : F) := Nat.cast_nonneg j
  have h4 : (0 : F) ≤ (j : F) - 1 + θ ∨ (j : F) = 0 := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · exact Or.inr (by simp [hj])
    · refine Or.inl ?_
      have : ((1 : ℕ) : F) ≤ (j : F) := by exact_mod_cast hj
      have : (0 : F) ≤ (j : F) - 1 := by simpa using this
      linarith
  have hpos : 0 < kappaT i j θ θ := by
    rw [kappaT]
    rcases h4 with h4 | h4
    · have : 0 < (i : F) * ((i : F) - 1 + θ) := mul_pos h1 (by linarith)
      have : 0 ≤ (j : F) * ((j : F) - 1 + θ) := mul_nonneg h3 h4
      linarith [mul_pos h1 (show (0:F) < (i : F) - 1 + θ by linarith)]
    · rw [h4]
      have : 0 < (i : F) * ((i : F) - 1 + θ) := mul_pos h1 (by linarith)
      linarith
  exact ne_of_gt hpos

theorem transcendence_fails_at_one :
    ¬ (∀ c d : ℤ, ((c : F) + (d : F) * (1 : F) = 0) → c = 0 ∧ d = 0) := by
  intro h
  have := h 1 (-1) (by push_cast; ring)
  exact one_ne_zero this.1

end Rhone.Algebra.Assembly
