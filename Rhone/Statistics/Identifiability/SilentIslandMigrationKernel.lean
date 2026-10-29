/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SilentWindowConditionalCovariance

/-! # Symmetric-island migration rows and their exact composition algebra -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.Identifiability.SilentWindow

def islandRow (k : ℕ) (z : ℝ) (x i : Fin (k + 2)) : ℝ :=
  z * (if x = i then 1 else 0) + (1 - z) / (k + 2 : ℝ)

lemma islandRow_sum (k : ℕ) (z : ℝ) (x : Fin (k + 2)) :
    ∑ i, islandRow k z x i = 1 := by
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  simp only [islandRow, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp
  ring

lemma islandRow_positive (k : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (x i : Fin (k + 2)) : 0 < islandRow k z x i := by
  have hp : 0 < (1 - z) / (k + 2 : ℝ) := div_pos (sub_pos.mpr hz1) (by positivity)
  by_cases h : x = i <;> simp only [islandRow, h, ite_true, ite_false, mul_one, mul_zero]
  · exact add_pos_of_nonneg_of_pos hz hp
  · simpa using hp

lemma islandRow_nonconstant (k : ℕ) {z : ℝ} (hz : 0 < z) (x : Fin (k + 2)) :
    ∃ i j, islandRow k z x i ≠ islandRow k z x j := by
  let y : Fin (k + 2) := ⟨if x.val = 0 then 1 else 0, by split_ifs <;> omega⟩
  have hxy : x ≠ y := by
    intro h
    have hh := congrArg Fin.val h
    dsimp only [y] at hh
    split_ifs at hh <;> omega
  refine ⟨x, y, ?_⟩
  intro he
  simp only [islandRow, ite_true, hxy, ite_false, mul_one, mul_zero, zero_add] at he
  linarith

lemma islandRow_compose (k : ℕ) (z w : ℝ) (x j : Fin (k + 2)) :
    (∑ i, islandRow k z x i * islandRow k w i j) = islandRow k (z * w) x j := by
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  simp only [islandRow, mul_add, add_mul, Finset.sum_add_distrib,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_ofNat]
  split_ifs <;> field_simp <;> ring

end Rhone.Statistics.Identifiability.SilentWindow
