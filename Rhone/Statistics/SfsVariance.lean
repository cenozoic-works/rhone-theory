/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsVariancePotential

/-!
# Second moment and variance of the marked Kingman site frequency spectrum

Source: fu1995, eq. (1)–(2), p. 174. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Filter

open Rhone.Combinatorics MarkovChain Probability
open scoped NNReal

theorem integral_kingmanBranchMutationKernel_sfs_sq (n i : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) :
    ∫ x, markedKingmanSfs n i (h, x) ^ 2 ∂kingmanBranchMutationKernel n θ h =
      ((θ : ℝ) / 2 * kingmanFiniteReward n (sfsBlockCount n i) h) ^ 2 +
        (θ : ℝ) / 2 * kingmanFiniteReward n (sfsBlockCount n i) h := by
  simp_rw [markedKingmanSfs_eq_weighted]
  change (∫ x : KingmanMutationBranch n → ℕ, (∑ b : KingmanMutationBranch n,
    (if b.2.card = i then (1 : ℝ) else 0) * (x b : ℝ)) ^ 2
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  have hw : ∀ b : KingmanMutationBranch n,
      (if b.2.card = i then (1 : ℝ) else 0) ^ 2 = if b.2.card = i then (1 : ℝ) else 0 := by
    intro b
    split_ifs <;> norm_num
  rw [pi_poisson_integral_weighted_count_sq]
  simp_rw [hw]
  rw [sum_kingmanBranchMutationRate_blockWeight n θ h
      (fun B => if B.card = i then (1 : ℝ) else 0), sfsBlockCount_eq_blockWeightReward]

theorem integrable_kingmanFiniteReward_sfsBlockCount_sq (n i : ℕ) :
    Integrable (fun h => kingmanFiniteReward n (sfsBlockCount n i) h ^ 2)
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  apply integrable_kingmanFiniteReward_sq
  intro π
  unfold sfsBlockCount
  exact Finset.sum_nonneg fun B _ => by split_ifs <;> norm_num

theorem integrable_markedKingmanSfs_sq (n i : ℕ) (θ : ℝ≥0) :
    Integrable (fun x => markedKingmanSfs n i x ^ 2) (markedKingmanLaw n θ) := by
  unfold markedKingmanLaw
  apply (Measure.integrable_compProd_iff
    ((measurable_markedKingmanSfs n i).pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun h => by
      simp_rw [markedKingmanSfs_eq_weighted]
      exact pi_poisson_integrable_weighted_count_sq (kingmanBranchMutationRate n θ h)
        (fun b => if b.2.card = i then (1 : ℝ) else 0)
  · simp_rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (markedKingmanSfs n i _)),
      integral_kingmanBranchMutationKernel_sfs_sq, mul_pow]
    exact ((integrable_kingmanFiniteReward_sfsBlockCount_sq n i).const_mul _).add
      ((integrable_kingmanFiniteReward_sfsBlockCount n i).const_mul _)

theorem markedKingmanSfs_second_moment {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫ x, markedKingmanSfs n i x ^ 2 ∂markedKingmanLaw n θ =
      (θ : ℝ) / i + (fuSigmaDiag n i + 1 / (i : ℝ) ^ 2) * (θ : ℝ) ^ 2 := by
  rw [show markedKingmanLaw n θ =
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
      (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd (integrable_markedKingmanSfs_sq n i θ)]
  simp_rw [integral_kingmanBranchMutationKernel_sfs_sq, mul_pow]
  rw [integral_add ((integrable_kingmanFiniteReward_sfsBlockCount_sq n i).const_mul _)
    ((integrable_kingmanFiniteReward_sfsBlockCount n i).const_mul _),
    integral_const_mul, integral_const_mul, integral_kingmanFiniteReward_sfsBlockCount_sq hi hin,
    integral_kingmanFiniteReward_sfsBlockCount hi hin]
  ring

/-- Source: fu1995, eq. (1)–(2), p. 174. -/
theorem markedKingmanSfs_variance {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanSfs n i) (markedKingmanLaw n θ) =
      (θ : ℝ) / i + fuSigmaDiag n i * (θ : ℝ) ^ 2 := by
  have hlp : MemLp (markedKingmanSfs n i) 2 (markedKingmanLaw n θ) :=
    (memLp_two_iff_integrable_sq (measurable_markedKingmanSfs n i).aestronglyMeasurable).2
      (integrable_markedKingmanSfs_sq n i θ)
  rw [variance_eq_sub hlp]
  change (∫ x, markedKingmanSfs n i x ^ 2 ∂markedKingmanLaw n θ) -
    (∫ x, markedKingmanSfs n i x ∂markedKingmanLaw n θ) ^ 2 = _
  rw [markedKingmanSfs_second_moment hi hin θ, markedKingmanSfs_mean hi hin θ]
  have hi0 : (i : ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  field_simp
  ring

end Rhone.Statistics
