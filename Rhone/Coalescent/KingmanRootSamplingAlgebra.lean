/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
/-! # Finite subset arithmetic for Kingman sample-root probabilities -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem sum_reciprocal_choose_supersets (N : ℕ) (S : Finset (Fin N)) :
    (∑ A : Finset (Fin N), if S ⊆ A then (N.choose A.card : ℝ)⁻¹ else 0) =
      ((N + 1 : ℕ) : ℝ) / (S.card + 1 : ℕ) := by
  classical
  have hs : S.card ≤ N := by simpa using card_le_card (subset_univ S)
  have hcS : (N.choose S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hs)
  have hbycard : ∀ k ∈ range (N + 1),
      (∑ A ∈ (univ : Finset (Fin N)).powersetCard k,
        if S ⊆ A then (N.choose A.card : ℝ)⁻¹ else 0) =
      (k.choose S.card : ℝ) / (N.choose S.card : ℝ) := by
    intro k hk
    have hkN : k ≤ N := by simpa using mem_range.mp hk
    have hsize : ∀ A ∈ (univ : Finset (Fin N)).powersetCard k,
        (if S ⊆ A then (N.choose A.card : ℝ)⁻¹ else 0) =
        (if S ⊆ A then (N.choose k : ℝ)⁻¹ else 0) := by
      intro A hA
      rw [(mem_powersetCard.mp hA).2]
    rw [sum_congr rfl hsize, ← sum_filter, sum_const, nsmul_eq_mul]
    by_cases hsk : S.card ≤ k
    · rw [card_filter_powersetCard_subset S univ k (subset_univ S) hsk,
        card_univ, Fintype.card_fin]
      have hm : (N.choose k : ℝ) * (k.choose S.card : ℝ) =
          (N.choose S.card : ℝ) * ((N - S.card).choose (k - S.card) : ℝ) := by
        exact_mod_cast Nat.choose_mul (n := N) hsk
      have hcK : (N.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hkN)
      apply (eq_div_iff hcS).mpr
      field_simp
      nlinarith [hm]
    · have he : ((univ : Finset (Fin N)).powersetCard k).filter (S ⊆ ·) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro A hA
        obtain ⟨hAk, hSA⟩ := mem_filter.mp hA
        have hc := card_le_card hSA
        rw [(mem_powersetCard.mp hAk).2] at hc
        exact hsk hc
      rw [he, card_empty, Nat.cast_zero, zero_mul, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have hsum : (∑ k ∈ range (N + 1), k.choose S.card) = N.succ.choose (S.card + 1) := by
    have hsub : Icc S.card N ⊆ range (N + 1) := by
      intro k hk
      exact mem_range.mpr (by have := (mem_Icc.mp hk).2; omega)
    rw [← sum_subset hsub (by
      intro k hk hkn
      apply Nat.choose_eq_zero_of_lt
      have hkN := mem_range.mp hk
      have hnot := mt mem_Icc.mpr hkn
      omega)]
    exact Nat.sum_Icc_choose N S.card
  rw [← powerset_univ, sum_powerset]
  simp only [card_univ, Fintype.card_fin]
  rw [sum_congr rfl hbycard]
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul, ← Nat.cast_sum, hsum, ← div_eq_mul_inv, ← div_eq_mul_inv]
  have hm := Nat.add_one_mul_choose_eq N S.card
  have hmR : ((N + 1 : ℕ) : ℝ) * (N.choose S.card : ℝ) =
      (N.succ.choose (S.card + 1) : ℝ) * (S.card + 1 : ℕ) := by exact_mod_cast hm
  have hs1 : ((S.card + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  apply (div_eq_div_iff hcS hs1).mpr
  simpa only [mul_comm] using hmR.symm
end Rhone.Coalescent
