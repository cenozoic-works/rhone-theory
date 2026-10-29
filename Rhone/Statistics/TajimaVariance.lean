/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.TajimaMarkedMoments
public import Rhone.Statistics.TajimaInitialPotentials
/-!
# Pairwise diversity mean and variance under the marked Kingman law

Source: tajima1983, eq. (29)–(30), p. 449; tajima1989, p. 585, eq. (6)–(7); kingman1982, sec. 1, eq.
(1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain
open scoped NNReal

/-- Source: tajima1989, p. 585, eq. (6). -/
theorem markedKingmanPi_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanPi n x ∂markedKingmanLaw n θ = θ := by
  rw [show markedKingmanLaw n θ =
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
      (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd (integrable_markedKingmanPi hn θ)]
  simp_rw [integral_kingmanBranchMutationKernel_pi hn]
  rw [integral_const_mul, integral_kingmanFiniteDiversityReward hn,
    kingmanDiversityReward_bot hn]
  ring

/-- Source: tajima1989, p. 585, eq. (6)–(7). -/
theorem markedKingmanPi_second_moment {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanPi n x ^ 2 ∂markedKingmanLaw n θ =
      (Rhone.Statistics.tajimaB1 n : ℝ) * θ +
        (1 + (Rhone.Statistics.tajimaB2 n : ℝ)) * (θ : ℝ) ^ 2 := by
  rw [show markedKingmanLaw n θ =
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
      (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd (integrable_markedKingmanPi_sq hn θ)]
  simp_rw [integral_kingmanBranchMutationKernel_pi_sq hn, mul_pow]
  rw [integral_add ((integrable_kingmanFiniteDiversityReward_sq hn).const_mul _)
    ((integrable_kingmanFiniteMutationReward hn).const_mul _),
    integral_const_mul, integral_const_mul, integral_kingmanFiniteDiversityReward_sq hn,
    integral_kingmanFiniteMutationReward hn, kingmanDiversitySquarePotential_bot hn,
    kingmanDiversityMutationPotential_bot hn]
  ring

/-- Source: tajima1983, eq. (30), p. 449; tajima1989, p. 585, eq. (7). -/
theorem markedKingmanPi_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, (markedKingmanPi n x - θ) ^ 2 ∂markedKingmanLaw n θ =
      (Rhone.Statistics.tajimaB1 n : ℝ) * θ +
        (Rhone.Statistics.tajimaB2 n : ℝ) * (θ : ℝ) ^ 2 := by
  have he : (fun x => (markedKingmanPi n x - θ) ^ 2) =
      fun x => (markedKingmanPi n x ^ 2 - (2 * (θ : ℝ)) * markedKingmanPi n x) +
        (θ : ℝ) ^ 2 := by
    funext x
    ring
  have hil : Integrable (fun x => (2 * (θ : ℝ)) * markedKingmanPi n x)
      (markedKingmanLaw n θ) := (integrable_markedKingmanPi hn θ).const_mul _
  have his : Integrable (fun x => markedKingmanPi n x ^ 2 -
      (2 * (θ : ℝ)) * markedKingmanPi n x) (markedKingmanLaw n θ) :=
    (integrable_markedKingmanPi_sq hn θ).sub hil
  rw [he, integral_add his (integrable_const _),
    integral_sub (integrable_markedKingmanPi_sq hn θ) hil,
    integral_const_mul, markedKingmanPi_mean hn θ, markedKingmanPi_second_moment hn θ]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring
end Rhone.Statistics
