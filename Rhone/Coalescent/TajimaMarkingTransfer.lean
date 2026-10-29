/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.TajimaBranchRewards
public import Rhone.Coalescent.KingmanFiniteRewards
public import Rhone.Probability.FinitePoissonCounts
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
/-!
# Finite branch marking transfer for the labelled Kingman law

Source: tajima1989, pp. 588–589, eq. (39)–(42). -/
@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset Rhone.Combinatorics MarkovChain
open scoped NNReal

noncomputable def kingmanFiniteReward (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
    (h : KingmanMutationHistory n) : ℝ :=
  ∑ k : Fin (n - 1), if h.1 k.val ∈ coalescedPartitions (Fin n) then 0
    else c (h.1 k.val) * max 0 ((partitionChain (Fin n)).holdTime h k.val)

private theorem sum_rate_weight (n : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) (w : Finset (Fin n) → ℝ) :
    ∑ b : KingmanMutationBranch n, w b.2 * kingmanBranchMutationRate n θ h b =
      (θ : ℝ) / 2 * kingmanFiniteReward n (fun π => ∑ B ∈ π.parts, w B) h := by
  classical
  rw [Fintype.sum_prod_type]
  unfold kingmanFiniteReward
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ B, w B * (if B ∈ (h.1 k.val).parts ∧ 1 < (h.1 k.val).parts.card then
    max 0 ((θ : ℝ) / 2 * (partitionChain (Fin n)).holdTime h k.val) else 0)) = _
  by_cases hk : h.1 k.val ∈ coalescedPartitions (Fin n)
  · have ht : ¬ 1 < (h.1 k.val).parts.card := by
      have := mem_coalescedPartitions.mp hk
      omega
    simp [ht, hk]
  · have ht : 1 < (h.1 k.val).parts.card := by
      have := mt mem_coalescedPartitions.mpr hk
      omega
    simp only [ht, and_true, hk, ↓reduceIte]
    have he (B : Finset (Fin n)) :
        w B * (if B ∈ (h.1 k.val).parts then
          max 0 ((θ : ℝ) / 2 * (partitionChain (Fin n)).holdTime h k.val) else 0) =
        if B ∈ (h.1 k.val).parts then
          ((θ : ℝ) / 2 * max 0 ((partitionChain (Fin n)).holdTime h k.val)) * w B else 0 := by
      split_ifs
      · rw [mul_max_of_nonneg 0 ((partitionChain (Fin n)).holdTime h k.val)
          (by positivity), mul_zero]
        ring
      · ring
    simp_rw [he]
    rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
    ring

theorem sum_kingmanBranchMutationRate_weight {n : ℕ} (hn : 2 ≤ n)
    (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    ∑ b : KingmanMutationBranch n,
      kingmanBranchPairWeight n b.2 * kingmanBranchMutationRate n θ h b =
    (θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityReward n) h := by
  rw [sum_rate_weight]
  congr 2
  funext π
  exact sum_kingmanBranchPairWeight hn π

theorem sum_kingmanBranchMutationRate_weight_sq {n : ℕ} (hn : 2 ≤ n)
    (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    ∑ b : KingmanMutationBranch n,
      kingmanBranchPairWeight n b.2 ^ 2 * kingmanBranchMutationRate n θ h b =
    (θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityMutationReward n) h := by
  rw [sum_rate_weight n θ h (fun B => kingmanBranchPairWeight n B ^ 2)]
  congr 2
  funext π
  exact sum_kingmanBranchPairWeight_sq hn π
end Rhone.Coalescent
