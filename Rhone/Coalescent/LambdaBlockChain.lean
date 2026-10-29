/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.LambdaRates
public import Rhone.Coalescent.KingmanPartition

/-! # The block-counting chain of a Λ-coalescent -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory Set Finset MarkovChain

variable (Λ : Measure ℝ)

noncomputable def lambdaMergeRate (b j : ℕ) : ℝ :=
  if 1 ≤ j ∧ j < b then (b.choose (b - j + 1) : ℝ) * lambdaRate Λ b (b - j + 1) else 0

theorem lambdaMergeRate_nonneg (b j : ℕ) : 0 ≤ lambdaMergeRate Λ b j := by
  unfold lambdaMergeRate
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (lambdaRate_nonneg _ _)
  · exact le_rfl

noncomputable def lambdaTotalRate (b : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 b, (b.choose k : ℝ) * lambdaRate Λ b k

theorem sum_lambdaMergeRate (n : ℕ) {b : ℕ} (hb : b ≤ n) :
    ∑ j : Fin (n + 1), lambdaMergeRate Λ b j = lambdaTotalRate Λ b := by
  rw [Fin.sum_univ_eq_sum_range (fun j => lambdaMergeRate Λ b j) (n + 1)]
  have h : ∑ j ∈ Finset.range (n + 1), lambdaMergeRate Λ b j =
      ∑ j ∈ Finset.Ico 1 b, lambdaMergeRate Λ b j := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro j hj
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_range]
      omega
    · intro j _ hj
      rw [Finset.mem_Ico] at hj
      unfold lambdaMergeRate
      rw [ite_eq_right (by omega)]
  rw [h, lambdaTotalRate]
  refine Finset.sum_nbij' (fun j => b - j + 1) (fun k => b - k + 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_Icc]
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ico]
    omega
  · intro j hj
    rw [Finset.mem_Ico] at hj
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    omega
  · intro j hj
    rw [Finset.mem_Ico] at hj
    unfold lambdaMergeRate
    rw [ite_eq_left (by omega)]

noncomputable def lambdaBlockQ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun b j =>
  lambdaMergeRate Λ b j - if j = b then ∑ i : Fin (n + 1), lambdaMergeRate Λ b i else 0

noncomputable def lambdaBlockChain (n : ℕ) : RateChain (Fin (n + 1)) where
  Q := lambdaBlockQ Λ n
  off_diag_nonneg b j h := by
    unfold lambdaBlockQ
    rw [ite_eq_right (Ne.symm h), sub_zero]
    exact lambdaMergeRate_nonneg Λ _ _
  row_sum b := by
    unfold lambdaBlockQ
    rw [Finset.sum_sub_distrib]
    simp

theorem lambdaBlockChain_Q (n : ℕ) : (lambdaBlockChain Λ n).Q = lambdaBlockQ Λ n := rfl

theorem lambdaBlockChain_rate (n : ℕ) (b : Fin (n + 1)) :
    (lambdaBlockChain Λ n).rate b = lambdaTotalRate Λ b := by
  have hb : (b : ℕ) ≤ n := Nat.lt_succ_iff.1 b.2
  have hz : lambdaMergeRate Λ b b = 0 := by
    unfold lambdaMergeRate
    rw [ite_eq_right (by omega)]
  simp [RateChain.rate, lambdaBlockChain_Q, lambdaBlockQ, hz, sum_lambdaMergeRate Λ n hb]

theorem lambdaMergeRate_dirac_zero (b j : ℕ) :
    lambdaMergeRate (Measure.dirac 0) b j = if j + 1 = b then (b.choose 2 : ℝ) else 0 := by
  unfold lambdaMergeRate
  by_cases h : 1 ≤ j ∧ j < b
  · rw [ite_eq_left h, lambdaRate_dirac_zero]
    by_cases hj : j + 1 = b
    · have e : b - j + 1 = 2 := by omega
      rw [ite_eq_left hj, e]
      simp
    · have e : 0 < b - j + 1 - 2 := by omega
      rw [ite_eq_right hj, zero_pow e.ne']
      simp
  · rw [ite_eq_right h]
    by_cases hj : j + 1 = b
    · rw [ite_eq_left hj]
      have : b < 2 := by omega
      rw [Nat.choose_eq_zero_of_lt this]
      simp
    · rw [ite_eq_right hj]

theorem lambdaTotalRate_dirac_zero (b : ℕ) :
    lambdaTotalRate (Measure.dirac 0) b = (b.choose 2 : ℝ) := by
  unfold lambdaTotalRate
  by_cases hb : 2 ≤ b
  · rw [Finset.sum_eq_single 2]
    · rw [lambdaRate_dirac_zero_two]
      simp
    · intro k hk hk2
      rw [Finset.mem_Icc] at hk
      rw [lambdaRate_dirac_zero_of_three_le _ (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hb⟩) h
  · have : Finset.Icc 2 b = ∅ := by
      ext k
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]
      omega
    rw [this, Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem lambdaBlockQ_dirac_zero (n : ℕ) : lambdaBlockQ (Measure.dirac 0) n = blockQ n := by
  ext b j
  have hb : (b : ℕ) ≤ n := Nat.lt_succ_iff.1 b.2
  unfold lambdaBlockQ blockQ
  simp only [Fin.ext_iff]
  rw [sum_lambdaMergeRate _ n hb, lambdaTotalRate_dirac_zero,
    lambdaMergeRate_dirac_zero, coalRate_cast_eq_choose]
  by_cases h1 : (j : ℕ) + 1 = b <;> by_cases h2 : (j : ℕ) = b <;> simp [h1, h2]

theorem lambdaBlockChain_dirac_zero (n : ℕ) :
    (lambdaBlockChain (Measure.dirac 0) n).Q = (blockChain n).Q :=
  lambdaBlockQ_dirac_zero n

end Rhone.Coalescent
