/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.ObservableAlgebra
public import Mathlib.Tactic.Linarith

/-! # Explicit score means under the finite polynomial site channel -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator

lemma patternMass_diagonal {K : ℕ} (hK : 0 < K) (x y z : ℝ) (a : Fin K) :
    patternMass K x y z a a a =
      (1 + ((K : ℝ) - 1)*(x + 2*y) + ((K : ℝ) - 1)*(K - 2)*z)/(K : ℝ)^3 := by
  have hn : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  simp only [patternMass, and_self, ite_true, mul_one]
  field_simp
  ring

lemma patternMass_total {K : ℕ} (hK : 0 < K) (x y z : ℝ) :
    (∑ a, ∑ b, ∑ c, patternMass K x y z a b c) = 1 := by
  have hn : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  simp_rw [patternMass_pair_marginal hK]
  simp [Finset.sum_add_distrib, ← Finset.sum_div]
  field_simp
  ring

lemma pairScore_marginal_mean {K : ℕ} (hK : 2 ≤ K) (x : ℝ) :
    (∑ a, ∑ b, pairScore K a b *
      ((1 - x)/(K : ℝ)^2 + x*(if a = b then 1 else 0)/K)) = x := by
  have hp : 0 < K := lt_of_lt_of_le (by decide : 0 < 2) hK
  have hn : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hd : (K : ℝ) - 1 ≠ 0 := by linarith
  have he (a b : Fin K) :
      pairScore K a b * ((1 - x)/(K : ℝ)^2 + x*(if a = b then 1 else 0)/K) =
        -(1 - x)/(((K : ℝ) - 1)*(K : ℝ)^2) +
          ((1 - x)/((K : ℝ)*(K - 1)) + x/K)*(if a = b then 1 else 0) := by
    unfold pairScore
    split_ifs <;> field_simp <;> ring
  simp_rw [he]
  simp [Finset.sum_add_distrib]
  field_simp
  ring

lemma pairScore_mean {K : ℕ} (hK : 2 ≤ K) (x y z : ℝ) :
    (∑ a, ∑ b, ∑ c, pairScore K a b * patternMass K x y z a b c) = x := by
  have hp : 0 < K := lt_of_lt_of_le (by decide : 0 < 2) hK
  simp_rw [← Finset.mul_sum, patternMass_pair_marginal hp]
  exact pairScore_marginal_mean hK x

lemma pairScore_noncherry_mean {K : ℕ} (hK : 2 ≤ K) (x y z : ℝ) :
    (∑ a, ∑ b, ∑ c, pairScore K a c * patternMass K x y z a b c) = y := by
  have hp : 0 < K := lt_of_lt_of_le (by decide : 0 < 2) hK
  have he (a : Fin K) :
      (∑ b, ∑ c, pairScore K a c * patternMass K x y z a b c) =
        ∑ c, pairScore K a c *((1 - y)/(K : ℝ)^2 + y*(if a = c then 1 else 0)/K) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, patternMass_noncherry_marginal hp]
  simp_rw [he]
  exact pairScore_marginal_mean hK y

lemma pairScore_other_mean {K : ℕ} (hK : 2 ≤ K) (x y z : ℝ) :
    (∑ a, ∑ b, ∑ c, pairScore K b c * patternMass K x y z a b c) = y := by
  rw [Finset.sum_comm]
  simp_rw [patternMass_swap K x y z]
  exact pairScore_noncherry_mean hK x y z

lemma patternMass_all_equal {K : ℕ} (hK : 0 < K) (x y z : ℝ) :
    (∑ a, ∑ b, ∑ c, (if a = b ∧ a = c then 1 else 0)*patternMass K x y z a b c) =
      (1 + ((K : ℝ) - 1)*(x + 2*y) + ((K : ℝ) - 1)*(K - 2)*z)/(K : ℝ)^2 := by
  have hn : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  simp only [ite_mul, one_mul, zero_mul, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const_zero]
  simp_rw [patternMass_diagonal hK]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Rhone.Statistics.ThreeSiteSeparator
