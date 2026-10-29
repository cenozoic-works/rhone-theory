/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SegregatingModel
public import Rhone.Coalescent.TajimaMarkingTransfer

/-!
# Total branch mutation rates and conditional Poisson count moments

Source: watterson1975, p. 264, eq. (2.2)–(2.3), (2.8). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Probability
open scoped NNReal

private theorem total_rate_weight (n : ℕ) (θ : ℝ≥0)
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

theorem sum_kingmanBranchMutationRate (n : ℕ) (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    ∑ b : KingmanMutationBranch n, (kingmanBranchMutationRate n θ h b : ℝ) =
      (θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h := by
  simpa only [one_mul, sum_const, nsmul_eq_mul, mul_one] using
    total_rate_weight n θ h (fun _ => 1)

theorem integral_kingmanBranchMutationKernel_segregating
    (n : ℕ) (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    (∫ x, markedKingmanSegregating n (h, x) ∂kingmanBranchMutationKernel n θ h) =
      (θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h := by
  change (∫ x, ∑ b : KingmanMutationBranch n, (x b : ℝ)
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  have hm := pi_poisson_integral_weighted_count (kingmanBranchMutationRate n θ h)
    (fun _ => (1 : ℝ))
  simp only [one_mul] at hm
  rw [hm, sum_kingmanBranchMutationRate]

theorem integral_kingmanBranchMutationKernel_segregating_sq
    (n : ℕ) (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    (∫ x, markedKingmanSegregating n (h, x) ^ 2 ∂kingmanBranchMutationKernel n θ h) =
      ((θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h) ^ 2 +
        (θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h := by
  change (∫ x, (∑ b : KingmanMutationBranch n, (x b : ℝ)) ^ 2
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  have hm := pi_poisson_integral_weighted_count_sq (kingmanBranchMutationRate n θ h)
    (fun _ => (1 : ℝ))
  simp only [one_mul, one_pow] at hm
  rw [hm, sum_kingmanBranchMutationRate]

end Rhone.Statistics
