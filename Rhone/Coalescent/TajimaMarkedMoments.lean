/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.TajimaFiniteMoments
/-!
# Moment transfer from independent Poisson marks to the genealogy law

Source: tajima1989, p. 585, eq. (6)–(7). -/
@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset Rhone.Combinatorics MarkovChain Probability Filter
open scoped NNReal

theorem markedKingmanPi_nonneg {n : ℕ} (hn : 2 ≤ n)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    0 ≤ markedKingmanPi n x := by
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (kingmanBranchPairWeight_nonneg hn _) (Nat.cast_nonneg _)

theorem integral_kingmanBranchMutationKernel_pi {n : ℕ} (hn : 2 ≤ n)
    (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    ∫ x, markedKingmanPi n (h, x) ∂kingmanBranchMutationKernel n θ h =
      (θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityReward n) h := by
  change (∫ x, ∑ b : KingmanMutationBranch n, kingmanBranchPairWeight n b.2 * (x b : ℝ)
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  rw [pi_poisson_integral_weighted_count, sum_kingmanBranchMutationRate_weight hn]

theorem integral_kingmanBranchMutationKernel_pi_sq {n : ℕ} (hn : 2 ≤ n)
    (θ : ℝ≥0) (h : KingmanMutationHistory n) :
    ∫ x, markedKingmanPi n (h, x) ^ 2 ∂kingmanBranchMutationKernel n θ h =
      ((θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityReward n) h) ^ 2 +
        (θ : ℝ) / 2 * kingmanFiniteReward n (kingmanDiversityMutationReward n) h := by
  change (∫ x, (∑ b : KingmanMutationBranch n, kingmanBranchPairWeight n b.2 * (x b : ℝ)) ^ 2
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  rw [pi_poisson_integral_weighted_count_sq, sum_kingmanBranchMutationRate_weight hn,
    sum_kingmanBranchMutationRate_weight_sq hn]

theorem integrable_markedKingmanPi {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    Integrable (markedKingmanPi n) (markedKingmanLaw n θ) := by
  unfold markedKingmanLaw
  apply (Measure.integrable_compProd_iff
    (measurable_markedKingmanPi n).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun h => pi_poisson_integrable_weighted_count
      (kingmanBranchMutationRate n θ h) (fun b => kingmanBranchPairWeight n b.2)
  · simp_rw [Real.norm_eq_abs, abs_of_nonneg (markedKingmanPi_nonneg hn _),
      integral_kingmanBranchMutationKernel_pi hn]
    exact (integrable_kingmanFiniteDiversityReward hn).const_mul _

theorem integrable_markedKingmanPi_sq {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    Integrable (fun x => markedKingmanPi n x ^ 2) (markedKingmanLaw n θ) := by
  unfold markedKingmanLaw
  apply (Measure.integrable_compProd_iff
    ((measurable_markedKingmanPi n).pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun h => pi_poisson_integrable_weighted_count_sq
      (kingmanBranchMutationRate n θ h) (fun b => kingmanBranchPairWeight n b.2)
  · simp_rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (markedKingmanPi n _)),
      integral_kingmanBranchMutationKernel_pi_sq hn, mul_pow]
    exact ((integrable_kingmanFiniteDiversityReward_sq hn).const_mul _).add
      ((integrable_kingmanFiniteMutationReward hn).const_mul _)
end Rhone.Coalescent
