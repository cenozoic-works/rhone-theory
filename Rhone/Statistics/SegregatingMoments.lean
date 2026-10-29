/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SegregatingMarkingTransfer
public import Rhone.Statistics.SegregatingExposure

/-!
# Segregating-site moments under the marked Kingman law

Source: watterson1975, p. 258, eq. (1.4a)–(1.5a); tajima1989, p. 585, eq. (1)–(2); kingman1982, sec.
1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Probability
open Filter
open scoped NNReal

private theorem length_eq_a1 (n : ℕ) : (expLength n : ℝ) = 2 * (tajimaA1 n : ℝ) := by
  have hq : expLength n = 2 * tajimaA1 n := by
    simpa only [tajimaA1] using expLength_eq n
  exact_mod_cast hq

private theorem length_variance_eq_a2 (n : ℕ) :
    (varLength n : ℝ) = 4 * (tajimaA2 n : ℝ) := by
  have hq : varLength n = 4 * tajimaA2 n := by
    simpa only [tajimaA2] using varLength_eq n
  exact_mod_cast hq

theorem integrable_markedKingmanSegregating (n : ℕ) (θ : ℝ≥0) :
    Integrable (markedKingmanSegregating n) (markedKingmanLaw n θ) := by
  unfold markedKingmanLaw
  apply (Measure.integrable_compProd_iff
    (measurable_markedKingmanSegregating n).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun h => by
      change Integrable (fun x : KingmanMutationBranch n → ℕ =>
        ∑ b : KingmanMutationBranch n, (x b : ℝ))
        (Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b)))
      simpa only [one_mul] using
        pi_poisson_integrable_weighted_count (kingmanBranchMutationRate n θ h)
          (fun _ => (1 : ℝ))
  · simp_rw [Real.norm_eq_abs, abs_of_nonneg (markedKingmanSegregating_nonneg n _),
      integral_kingmanBranchMutationKernel_segregating]
    exact (integrable_kingmanFiniteLength n).const_mul _

theorem integrable_markedKingmanSegregating_sq (n : ℕ) (θ : ℝ≥0) :
    Integrable (fun x => markedKingmanSegregating n x ^ 2) (markedKingmanLaw n θ) := by
  unfold markedKingmanLaw
  apply (Measure.integrable_compProd_iff
    ((measurable_markedKingmanSegregating n).pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun h => by
      change Integrable (fun x : KingmanMutationBranch n → ℕ =>
        (∑ b : KingmanMutationBranch n, (x b : ℝ)) ^ 2)
        (Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b)))
      simpa only [one_mul] using
        pi_poisson_integrable_weighted_count_sq (kingmanBranchMutationRate n θ h)
          (fun _ => (1 : ℝ))
  · simp_rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (markedKingmanSegregating n _)),
      integral_kingmanBranchMutationKernel_segregating_sq, mul_pow]
    exact ((integrable_kingmanFiniteLength_sq n).const_mul _).add
      ((integrable_kingmanFiniteLength n).const_mul _)

/-- Source: watterson1975, p. 258, eq. (1.4a); tajima1989, p. 585, eq. (1)–(2). -/
theorem markedKingmanSegregating_mean {n : ℕ} (_hn : 2 ≤ n) (θ : ℝ≥0) :
    (∫ x, markedKingmanSegregating n x ∂markedKingmanLaw n θ) =
      (θ : ℝ) * (tajimaA1 n : ℝ) := by
  rw [show markedKingmanLaw n θ =
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
      (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd (integrable_markedKingmanSegregating n θ)]
  simp_rw [integral_kingmanBranchMutationKernel_segregating]
  rw [integral_const_mul, integral_kingmanFiniteLength n, length_eq_a1 n]
  ring

theorem markedKingmanSegregating_second_moment {n : ℕ} (_hn : 2 ≤ n) (θ : ℝ≥0) :
    (∫ x, markedKingmanSegregating n x ^ 2 ∂markedKingmanLaw n θ) =
      (θ : ℝ) * (tajimaA1 n : ℝ) +
        (θ : ℝ) ^ 2 * ((tajimaA1 n : ℝ) ^ 2 + (tajimaA2 n : ℝ)) := by
  rw [show markedKingmanLaw n θ =
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
      (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd (integrable_markedKingmanSegregating_sq n θ)]
  simp_rw [integral_kingmanBranchMutationKernel_segregating_sq, mul_pow]
  rw [integral_add ((integrable_kingmanFiniteLength_sq n).const_mul _)
    ((integrable_kingmanFiniteLength n).const_mul _),
    integral_const_mul, integral_const_mul, integral_kingmanFiniteLength_sq n,
    integral_kingmanFiniteLength n, length_eq_a1 n, length_variance_eq_a2 n]
  ring

/-- Source: watterson1975, p. 258, eq. (1.5a); tajima1989, p. 585, eq. (1)–(2). -/
theorem markedKingmanSegregating_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanSegregating n) (markedKingmanLaw n θ) =
      (θ : ℝ) * (tajimaA1 n : ℝ) + (θ : ℝ) ^ 2 * (tajimaA2 n : ℝ) := by
  have hlp : MemLp (markedKingmanSegregating n) 2 (markedKingmanLaw n θ) :=
    (memLp_two_iff_integrable_sq (measurable_markedKingmanSegregating n).aestronglyMeasurable).2
      (integrable_markedKingmanSegregating_sq n θ)
  rw [variance_eq_sub hlp]
  change (∫ x, markedKingmanSegregating n x ^ 2 ∂markedKingmanLaw n θ) -
    (∫ x, markedKingmanSegregating n x ∂markedKingmanLaw n θ) ^ 2 = _
  rw [markedKingmanSegregating_second_moment hn θ, markedKingmanSegregating_mean hn θ]
  ring

end Rhone.Statistics
