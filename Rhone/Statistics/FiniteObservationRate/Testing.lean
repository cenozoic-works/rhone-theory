/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FiniteObservationRate.Tensor

/-! # Inverse-square necessary iid sample budget on a fixed finite alphabet -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.FiniteObservationRate
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X] [Nonempty X]

omit [Fintype X] [Nonempty X] in
theorem sqrt_difference_sq_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ (p - q) ^ 2 / q := by
  have hsp := Real.sqrt_nonneg p
  have hsq := Real.sqrt_nonneg q
  have hp2 := Real.sq_sqrt hp
  have hq2 := Real.sq_sqrt hq.le
  have hf : (p - q) ^ 2 =
      (Real.sqrt p - Real.sqrt q) ^ 2 * (Real.sqrt p + Real.sqrt q) ^ 2 := by
    calc
      _ = (Real.sqrt p ^ 2 - Real.sqrt q ^ 2) ^ 2 := by rw [hp2, hq2]
      _ = _ := by ring
  rw [le_div_iff₀ hq, hf]
  have hs : q ≤ (Real.sqrt p + Real.sqrt q) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)

omit [Nonempty X] in
theorem hellinger_coordinate_bound (P Q : Law X) {b C ε : ℝ}
    (hb : 0 < b)
    (hQ : ∀ x, b ≤ Q.mass x) (hclose : ∀ x, |P.mass x - Q.mass x| ≤ C * ε) :
    hellingerSq P Q ≤ Fintype.card X * (C ^ 2 * ε ^ 2 / b) := by
  have ha (x : X) : (Real.sqrt (P.mass x) - Real.sqrt (Q.mass x)) ^ 2 ≤
      C ^ 2 * ε ^ 2 / b := by
    have hs := sqrt_difference_sq_le (P.nonneg x) (hb.trans_le (hQ x))
    have hsq : (P.mass x - Q.mass x) ^ 2 ≤ C ^ 2 * ε ^ 2 := by
      have ht := mul_self_le_mul_self (abs_nonneg _) (hclose x)
      nlinarith [sq_abs (P.mass x - Q.mass x)]
    exact hs.trans ((div_le_div_of_nonneg_left (sq_nonneg _) hb (hQ x)).trans
      (div_le_div_of_nonneg_right hsq hb.le))
  unfold hellingerSq
  calc
    _ ≤ ∑ _x : X, C ^ 2 * ε ^ 2 / b := Finset.sum_le_sum fun x _ => ha x
    _ = _ := by simp

theorem iid_necessary_inverse_square (P Q : Law X) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {b C ε δ : ℝ} (hb : 0 < b) (hC : 0 < C) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hQ : ∀ x, b ≤ Q.mass x) (hclose : ∀ x, |P.mass x - Q.mass x| ≤ C * ε)
    (hadvantage : δ ≤ rejection (iid P N) φ - rejection (iid Q N) φ) :
    δ ^ 2 * b / (Fintype.card X * C ^ 2 * ε ^ 2) ≤ (N : ℝ) := by
  have hd := rejection_difference_le (iid P N) (iid Q N) φ hφ
  have hdtv : δ ≤ totalVariation (iid P N) (iid Q N) :=
    hadvantage.trans ((le_abs_self _).trans hd)
  have hsq := mul_self_le_mul_self hδ hdtv
  have ht := iid_tv_sq_le P Q N
  have hh := mul_le_mul_of_nonneg_left (hellinger_coordinate_bound P Q hb hQ hclose)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hden : 0 < (Fintype.card X : ℝ) * C ^ 2 * ε ^ 2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hh' : δ ^ 2 ≤ (N : ℝ) * (Fintype.card X * (C ^ 2 * ε ^ 2 / b)) := by
    nlinarith
  have hbnd := (le_div_iff₀ hb).mp
    (show δ ^ 2 ≤ (N : ℝ) * Fintype.card X * C ^ 2 * ε ^ 2 / b by
      calc
        _ ≤ (N : ℝ) * (Fintype.card X * (C ^ 2 * ε ^ 2 / b)) := hh'
        _ = _ := by ring)
  nlinarith

end Rhone.Statistics.FiniteObservationRate
