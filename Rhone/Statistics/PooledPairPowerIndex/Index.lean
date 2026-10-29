/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LinkedPairMoments.Expansion
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Pooled finite-category index, including unreachable categories -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.PooledPairPowerIndex
open DependenceBudget
variable {X : Type*} [Fintype X]

def categoryIndex (P Q : Law X) (x : X) : ℝ :=
  (P.mass x - Q.mass x) ^ 2 / (2 * (P.mass x + Q.mass x))

def pooledIndex (P Q : Law X) : ℝ := ∑ x, categoryIndex P Q x

theorem category_index_nonneg (P Q : Law X) (x : X) : 0 ≤ categoryIndex P Q x :=
  div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (add_nonneg (P.nonneg x) (Q.nonneg x)))

theorem category_index_zero_iff (P Q : Law X) (x : X) :
    categoryIndex P Q x = 0 ↔ P.mass x = Q.mass x := by
  have hp := P.nonneg x
  have hq := Q.nonneg x
  unfold categoryIndex
  constructor
  · intro h
    rcases (div_eq_zero_iff).mp h with h | h
    · nlinarith [sq_nonneg (P.mass x - Q.mass x)]
    · nlinarith
  · intro h
    simp [h]

theorem pooled_index_nonneg (P Q : Law X) : 0 ≤ pooledIndex P Q :=
  Finset.sum_nonneg fun x _ => category_index_nonneg P Q x

theorem pooled_index_zero_iff (P Q : Law X) : pooledIndex P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    apply LinkedPairMoments.finite_law_ext
    intro x
    apply (category_index_zero_iff P Q x).mp
    have hi : categoryIndex P Q x ≤ pooledIndex P Q :=
      Finset.single_le_sum (fun y _ => category_index_nonneg P Q y) (Finset.mem_univ x)
    exact le_antisymm (h ▸ hi) (category_index_nonneg P Q x)
  · rintro rfl
    simp [pooledIndex, categoryIndex]

theorem category_index_le (P Q : Law X) (x : X) :
    categoryIndex P Q x ≤ (P.mass x + Q.mass x) / 2 := by
  have hp := P.nonneg x
  have hq := Q.nonneg x
  by_cases hz : P.mass x + Q.mass x = 0
  · have he : P.mass x = Q.mass x := by linarith
    simp [categoryIndex, he, hq]
  · have hs : 0 < P.mass x + Q.mass x := lt_of_le_of_ne (add_nonneg hp hq) (Ne.symm hz)
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hs)).mpr
    nlinarith [mul_nonneg hp hq]

theorem pooled_index_le_one (P Q : Law X) : pooledIndex P Q ≤ 1 := by
  calc
    _ ≤ ∑ x, (P.mass x + Q.mass x) / 2 :=
      Finset.sum_le_sum fun x _ => category_index_le P Q x
    _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, P.total, Q.total]; norm_num

end Rhone.Statistics.PooledPairPowerIndex
