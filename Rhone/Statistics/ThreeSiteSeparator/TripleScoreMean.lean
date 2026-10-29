/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.ObservableExpectations

/-! # The bounded third-order allele contrast has the internal-branch mean -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator

lemma tripleScore_pair_identity {K : ℕ} (hK : 3 ≤ K) (a b c : Fin K) :
    tripleScore K a b c =
      ((K : ℝ)^2*(if a = b ∧ a = c then 1 else 0) -
        ((K : ℝ) - 1)*(pairScore K a b + pairScore K a c + pairScore K b c) - 1)/
        (((K : ℝ) - 1)*(K - 2)) := by
  have hk : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : (K : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (K : ℝ) - 2 ≠ 0 := by linarith
  unfold tripleScore pairScore
  field_simp
  ring

lemma tripleScore_mean {K : ℕ} (hK : 3 ≤ K) (x y z : ℝ) :
    (∑ a, ∑ b, ∑ c, tripleScore K a b c * patternMass K x y z a b c) = z := by
  have hp : 0 < K := lt_of_lt_of_le (by decide : 0 < 3) hK
  have ht : 2 ≤ K := le_trans (by decide : 2 ≤ 3) hK
  have hk : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have h0 : (K : ℝ) ≠ 0 := by linarith
  have h1 : (K : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (K : ℝ) - 2 ≠ 0 := by linarith
  have he (a b c : Fin K) :
      tripleScore K a b c * patternMass K x y z a b c =
        ((K : ℝ)^2*((if a = b ∧ a = c then 1 else 0)*patternMass K x y z a b c) -
          ((K : ℝ) - 1)*(pairScore K a b*patternMass K x y z a b c +
            pairScore K a c*patternMass K x y z a b c +
            pairScore K b c*patternMass K x y z a b c) - patternMass K x y z a b c)/
          (((K : ℝ) - 1)*(K - 2)) := by
    rw [tripleScore_pair_identity hK]
    ring
  simp_rw [he]
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hab := pairScore_mean ht x y z
  simp_rw [← Finset.mul_sum] at hab
  rw [patternMass_all_equal hp, hab, pairScore_noncherry_mean ht,
    pairScore_other_mean ht, patternMass_total hp]
  field_simp
  ring

end Rhone.Statistics.ThreeSiteSeparator
