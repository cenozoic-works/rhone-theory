/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanLeafDepthExpectation
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Algebra.BigOperators.Intervals
/-!
# Sackin's sum of leaf depths under chronological Kingman histories

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def treeSackin {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) : ℕ := ∑ x, leafCladeDepth G x
theorem kingman_sackin_expectation (n : ℕ) (hn : 1 ≤ n) :
    Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => (treeSackin G : ℝ)) =
      2 * (n : ℝ) * (((harmonic n : ℚ) : ℝ) - 1) := by
  have hdepth : ∀ x : Fin n, leafCladeDepth (ADR11.singletonForest n) x = 0 := by
    intro x
    have he : (ADR11.singletonForest n).filter (fun C => x ∈ C) = {{x}} := by
      ext C
      simp only [mem_filter, ADR11.singletonForest, mem_image, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨⟨y, rfl⟩, hx⟩
        have he := mem_singleton.mp hx
        rw [he]
      · intro he
        subst C
        exact ⟨⟨x, rfl⟩, mem_singleton_self x⟩
    unfold leafCladeDepth
    rw [he]
    simp
  have hpay : ∀ x : Fin n,
      Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
          (fun G => (leafCladeDepth G x : ℝ)) =
        2 * ∑ j ∈ range (n - 1), (1 : ℝ) / (n - j : ℕ) := by
    intro x
    rw [history_payoff_leaf_depth _ (ADR11.isForest_singletonForest n) x
      (by rw [ADR11.absorb_lineages_singletonForest]; exact mem_univ x)
      (n - 1) (by rw [ADR11.card_roots_singletonForest]),
      hdepth x, Nat.cast_zero, zero_add, ADR11.card_roots_singletonForest]
  have hrev : (∑ j ∈ range (n - 1), (1 : ℝ) / (n - j : ℕ)) =
      ∑ j ∈ range (n - 1), (1 : ℝ) / (j + 2 : ℕ) := by
    calc
      _ = ∑ j ∈ range (n - 1), (1 : ℝ) / ((n - 1 - 1 - j) + 2 : ℕ) := by
        apply sum_congr rfl
        intro j hj
        have hjn := mem_range.mp hj
        congr 2
        omega
      _ = _ := sum_range_reflect (fun j => (1 : ℝ) / (j + 2 : ℕ)) (n - 1)
  have hh : ((harmonic n : ℚ) : ℝ) =
      (∑ j ∈ range (n - 1), (1 : ℝ) / (j + 2 : ℕ)) + 1 := by
    rw [harmonic, show n = n - 1 + 1 by omega, sum_range_succ']
    simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Nat.zero_add, Nat.cast_one, inv_one, one_div]
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel, Rat.cast_one]
  have hs : Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
      (fun G => (treeSackin G : ℝ)) =
      ∑ x : Fin n, Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1)
        (fun G => (leafCladeDepth G x : ℝ)) := by
    unfold Combinatorics.historyPayoff treeSackin
    simp_rw [Nat.cast_sum, mul_sum]
    exact sum_comm
  rw [hs, sum_congr rfl (fun x _ => hpay x), sum_const, nsmul_eq_mul,
    card_univ, Fintype.card_fin, hrev, hh]
  ring
end Rhone.Coalescent
