/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TajimaVarianceModel
public import Rhone.Coalescent.KingmanDiversitySquare

/-!
# Branch pair weights and labelled Kingman diversity rewards

Source: tajima1989, p. 586, eq. (10)–(12). -/

@[expose] public section
namespace Rhone.Coalescent
open Finset Rhone.Combinatorics MarkovChain

theorem kingmanBranchPairWeight_nonneg {n : ℕ} (hn : 2 ≤ n) (B : Finset (Fin n)) :
    0 ≤ kingmanBranchPairWeight n B := by
  have hB : (B.card : ℝ) ≤ n := by
    exact_mod_cast (by simpa using B.card_le_univ : B.card ≤ n)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold kingmanBranchPairWeight
  exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hB))
    (mul_nonneg (by linarith) (by linarith))

/-- Source: tajima1989, p. 586, eq. (12). -/
theorem kingmanBranchPairWeight_eq_mass {n : ℕ} (hn : 2 ≤ n) (B : Finset (Fin n)) :
    kingmanBranchPairWeight n B = (2 * n / ((n : ℝ) - 1)) *
      ((B.card : ℝ) / n) * (1 - (B.card : ℝ) / n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  unfold kingmanBranchPairWeight
  field_simp

theorem sum_kingmanBranchPairWeight {n : ℕ} (hn : 2 ≤ n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ B ∈ π.parts, kingmanBranchPairWeight n B = Rhone.Coalescent.kingmanDiversityReward n π := by
  simp_rw [kingmanBranchPairWeight_eq_mass hn]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  have he : (∑ B ∈ π.parts, (B.card : ℝ) / n * (1 - (B.card : ℝ) / n)) =
      1 - kingmanBlockMassMoment n 2 π := by
    simp_rw [mul_sub, mul_one, ← pow_two]
    rw [Finset.sum_sub_distrib, sum_kingmanBlockMass (by omega : 0 < n)]
    rfl
  rw [he]
  rfl

theorem sum_kingmanBranchPairWeight_sq {n : ℕ} (hn : 2 ≤ n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ B ∈ π.parts, kingmanBranchPairWeight n B ^ 2 =
      Rhone.Coalescent.kingmanDiversityMutationReward n π := by
  simp_rw [kingmanBranchPairWeight_eq_mass hn]
  have he (B : Finset (Fin n)) :
      ((2 * n / ((n : ℝ) - 1)) * ((B.card : ℝ) / n) * (1 - (B.card : ℝ) / n)) ^ 2 =
      (2 * n / ((n : ℝ) - 1)) ^ 2 *
        (((B.card : ℝ) / n) ^ 2 - 2 * ((B.card : ℝ) / n) ^ 3 + ((B.card : ℝ) / n) ^ 4) := by
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold kingmanDiversityMutationReward kingmanBlockMassMoment
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

end Rhone.Coalescent
