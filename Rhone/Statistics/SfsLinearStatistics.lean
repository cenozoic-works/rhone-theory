/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsMarkedSpectrum

/-!
# Linear statistics of the site frequency spectrum under the marked Kingman law

Source: fu1995, eq. 22; tajima1989, p. 586, eq. (10)–(12). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory Finset Coalescent Rhone.Combinatorics MarkovChain
open scoped NNReal

private theorem kingmanMutationBranch_card_le (n : ℕ) (b : KingmanMutationBranch n) :
    b.2.card ≤ n := by
  have h := Finset.card_le_univ b.2
  rwa [Fintype.card_fin] at h

private theorem sum_Icc_one_cast (m : ℕ) :
    ∑ i ∈ Icc 1 m, (i : ℝ) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- Source: fu1995, eq. 22. -/
theorem markedKingmanSegregating_eq_sum_sfs (n : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    markedKingmanSegregating n x = ∑ i ∈ range (n + 1), markedKingmanSfs n i x := by
  unfold markedKingmanSegregating markedKingmanSfs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hmem : b.2.card ∈ range (n + 1) := by
    rw [Finset.mem_range]
    have := kingmanMutationBranch_card_le n b
    omega
  rw [Finset.sum_ite_eq]
  simp only [hmem, ↓reduceIte]

/-- Source: tajima1989, p. 586, eq. (11)–(12); fu1995, eq. 22. -/
theorem markedKingmanPi_eq_sum_sfs (n : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    markedKingmanPi n x =
      ∑ i ∈ Icc 1 (n - 1),
        (2 * (i : ℝ) * ((n : ℝ) - i) / ((n : ℝ) * ((n : ℝ) - 1))) * markedKingmanSfs n i x := by
  unfold markedKingmanPi markedKingmanSfs
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_ite_eq]
  unfold kingmanBranchPairWeight
  split_ifs with hb
  · rfl
  · rw [Finset.mem_Icc] at hb
    have hle := kingmanMutationBranch_card_le n b
    have hcases : b.2.card = 0 ∨ b.2.card = n := by omega
    rcases hcases with h0 | hn
    · rw [h0, Nat.cast_zero, mul_zero, zero_mul, zero_div, zero_mul]
    · rw [hn, sub_self, mul_zero, zero_div, zero_mul]

/-- Source: fu1995, eq. 22; fay_wu2000, p. 1406, eq. (3). -/
theorem markedKingman_fayWu_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, (2 / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ i ∈ Icc 1 (n - 1), (i : ℝ) ^ 2 * markedKingmanSfs n i x ∂markedKingmanLaw n θ =
      (θ : ℝ) := by
  rw [integral_const_mul, integral_finsetSum _ fun i _ =>
    (integrable_markedKingmanSfs n i θ).const_mul _]
  have hterm : ∀ i ∈ Icc 1 (n - 1),
      ∫ x, (i : ℝ) ^ 2 * markedKingmanSfs n i x ∂markedKingmanLaw n θ = (θ : ℝ) * (i : ℝ) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : (i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [integral_const_mul, markedKingmanSfs_mean hi.1 (by omega)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_Icc_one_cast,
    Nat.cast_sub (by omega), Nat.cast_one]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp
  ring

/-- Source: fu1995, eq. 22. -/
theorem markedKingman_folded_sfs_mean {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫ x, (markedKingmanSfs n i x + markedKingmanSfs n (n - i) x) ∂markedKingmanLaw n θ =
      (θ : ℝ) * (1 / (i : ℝ) + 1 / ((n : ℝ) - i)) := by
  rw [integral_add (integrable_markedKingmanSfs n i θ) (integrable_markedKingmanSfs n (n - i) θ),
    markedKingmanSfs_mean hi hin, markedKingmanSfs_mean (by omega) (by omega),
    Nat.cast_sub hin.le]
  ring

end Rhone.Statistics
