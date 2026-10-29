/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FiniteObservationRate.Testing

/-! # Rational Hellinger bound used by the candidate certificate -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ConcretePanGrid
open DependenceBudget DependentPairedTest FiniteObservationRate

theorem sqrt_difference_sq_le_sum {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p + q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ (p - q) ^ 2 / (p + q) := by
  have hp2 := Real.sq_sqrt hp
  have hq2 := Real.sq_sqrt hq
  have hprod := mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg q)
  have hf : (p - q) ^ 2 =
      (Real.sqrt p - Real.sqrt q) ^ 2 * (Real.sqrt p + Real.sqrt q) ^ 2 := by
    calc
      _ = (Real.sqrt p ^ 2 - Real.sqrt q ^ 2) ^ 2 := by rw [hp2, hq2]
      _ = _ := by ring
  rw [le_div_iff₀ hs, hf]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith

theorem hellinger_rational_bound {X : Type*} [Fintype X] (P Q : Law X)
    (hs : ∀ x, 0 < P.mass x + Q.mass x) :
    hellingerSq P Q ≤ ∑ x, (P.mass x - Q.mass x) ^ 2 / (P.mass x + Q.mass x) := by
  exact Finset.sum_le_sum fun x _ => sqrt_difference_sq_le_sum (P.nonneg x) (Q.nonneg x) (hs x)

theorem finite_candidate_obstruction {X : Type*} [Fintype X] (P Q : Law X)
    (hs : ∀ x, 0 < P.mass x + Q.mass x)
    (hbound : (∑ x, (P.mass x - Q.mass x) ^ 2 / (P.mass x + Q.mass x)) <
      9 / (16 * 38318671)) {N : ℕ} (hN : N ≤ 38318671)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hsize : rejection (iid Q N) φ ≤ 1 / 20) :
    rejection (iid P N) φ < 4 / 5 := by
  have hH := hellinger_rational_bound P Q hs
  have hTV := iid_tv_sq_le P Q N
  have hdiff := rejection_difference_le (iid P N) (iid Q N) φ hφ
  have hN' : (N : ℝ) ≤ 38318671 := by exact_mod_cast hN
  have hH0 := hellinger_nonneg P Q
  have hscale := mul_le_mul_of_nonneg_right hN' hH0
  have hstrict : (38318671 : ℝ) * hellingerSq P Q < 9 / 16 := by
    have hlt := hH.trans_lt hbound
    linarith
  have hupper : totalVariation (iid P N) (iid Q N) < 3 / 4 := by
    nlinarith [sq_nonneg (totalVariation (iid P N) (iid Q N) - 3 / 4)]
  have hle := le_abs_self (rejection (iid P N) φ - rejection (iid Q N) φ)
  linarith

end Rhone.Statistics.ConcretePanGrid
