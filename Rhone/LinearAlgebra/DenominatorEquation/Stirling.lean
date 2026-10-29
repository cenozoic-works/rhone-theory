/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Unsigned Stirling numbers of the first kind -/

@[expose] public section

namespace Rhone.LinearAlgebra.DenominatorEquation

open Polynomial

def stirling1 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => stirling1 n k + n * stirling1 n (k + 1)

@[simp] theorem stirling1_zero_zero : stirling1 0 0 = 1 := rfl

@[simp] theorem stirling1_zero_succ (k : ℕ) : stirling1 0 (k + 1) = 0 := rfl

@[simp] theorem stirling1_succ_zero (n : ℕ) : stirling1 (n + 1) 0 = 0 := rfl

theorem stirling1_succ_succ (n k : ℕ) :
    stirling1 (n + 1) (k + 1) = stirling1 n k + n * stirling1 n (k + 1) := rfl

theorem stirling1_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → stirling1 n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  | succ n ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [stirling1_succ_succ, ih (by omega), ih (by omega), Nat.mul_zero]

@[simp] theorem stirling1_self : ∀ n : ℕ, stirling1 n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [stirling1_succ_succ, stirling1_self n, stirling1_eq_zero_of_lt (by omega), Nat.mul_zero]

theorem stirling1_pos : ∀ {n k : ℕ}, 1 ≤ k → k ≤ n → 0 < stirling1 n k := by
  intro n
  induction n with
  | zero => intro k h1 h2; omega
  | succ n ih =>
    intro k h1 h2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [stirling1_succ_succ]
    rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have h1 : 0 < stirling1 n 1 := ih (le_refl 1) hn
        have h2 : 0 < n * stirling1 n (0 + 1) := Nat.mul_pos hn (by simpa using h1)
        omega
    · have := ih hk' (by omega)
      omega

variable {R : Type*} [CommRing R]

theorem coeff_linear_mul (α β : R) (p : Polynomial R) (n : ℕ) :
    ((C α + C β * X) * p).coeff (n + 1) = α * p.coeff (n + 1) + β * p.coeff n := by
  rw [add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_mul]

theorem prod_coeff_stirling (a : R) : ∀ (n k : ℕ),
    (∏ t ∈ Finset.range (n + 1), (C a + C ((t : ℕ) : R) * X)).coeff k
      = (stirling1 (n + 1) (n + 1 - k) : R) * a ^ (n + 1 - k) := by
  intro n
  induction n with
  | zero =>
    intro k
    rw [Finset.prod_range_one]
    simp only [Nat.cast_zero, map_zero, zero_mul, add_zero, coeff_C]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [ite_eq_right (by omega), show 0 + 1 - k = 0 from by omega]
      simp
  | succ n ih =>
    intro k
    rw [Finset.prod_range_succ, mul_comm]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [mul_coeff_zero, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C_zero, ih 0]
      simp only [mul_zero, add_zero, Nat.sub_zero, stirling1_self]
      push_cast
      ring
    · obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
      rw [coeff_linear_mul, ih (e + 1), ih e]
      rcases Nat.lt_or_ge n e with he | he
      · have h1 : n + 1 - (e + 1) = 0 := by omega
        have h2 : n + 1 - e = 0 := by omega
        have h3 : n + 1 + 1 - (e + 1) = 0 := by omega
        rw [h1, h2, h3]
        simp
      · have h1 : n + 1 - (e + 1) = n - e := by omega
        have h2 : n + 1 - e = (n - e) + 1 := by omega
        have h3 : n + 1 + 1 - (e + 1) = (n - e) + 1 := by omega
        have hrec : stirling1 (n + 1 + 1) ((n - e) + 1)
            = stirling1 (n + 1) (n - e) + (n + 1) * stirling1 (n + 1) ((n - e) + 1) :=
          stirling1_succ_succ (n + 1) (n - e)
        rw [h1, h2, h3, hrec]
        push_cast
        ring

end Rhone.LinearAlgebra.DenominatorEquation
