/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.TajimaMarkingTransfer
/-!
# First and second moments of finite Kingman branch exposure

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7); tajima1989, p. 585, eq. (6)–(7). -/
@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset Rhone.Combinatorics MarkovChain Filter

theorem measurable_kingmanFiniteReward (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
    Measurable (kingmanFiniteReward n c) := by
  classical
  unfold kingmanFiniteReward
  apply Finset.measurable_sum
  intro k _
  have hm : Measurable (fun h : KingmanMutationHistory n => h.1 k.val) := by fun_prop
  apply Measurable.ite (hm (MeasurableSet.of_discrete)) measurable_const
  have hc : Measurable c := Measurable.of_discrete
  have hr : Measurable (partitionChain (Fin n)).rate := Measurable.of_discrete
  unfold Rhone.MarkovChain.RateChain.holdTime
  fun_prop

theorem kingmanFiniteReward_nonneg (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π)
    (h : KingmanMutationHistory n) : 0 ≤ kingmanFiniteReward n c h := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> first | exact le_rfl | exact mul_nonneg (hc _) (le_max_left _ _)

private theorem lintegral_finiteReward (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π) :
    ∫⁻ h, ENNReal.ofReal (kingmanFiniteReward n c h)
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    ∫⁻ h, (partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n)) c h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
  apply lintegral_congr_ae
  filter_upwards [partition_costBefore_eq_finite_clamped_sum n c hc] with h hh
  exact hh.symm

private theorem lintegral_finiteDiversity_sq {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ h, ENNReal.ofReal (kingmanFiniteReward n (kingmanDiversityReward n) h ^ 2)
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    ENNReal.ofReal (kingmanDiversitySquarePotential n ⊥) := by
  rw [← lintegral_kingmanDiversityReward_sq hn]
  apply lintegral_congr_ae
  filter_upwards [partition_costBefore_eq_finite_clamped_sum n
    (kingmanDiversityReward n) (kingmanDiversityReward_nonneg hn)] with h hh
  rw [hh]
  exact (ENNReal.ofReal_pow (kingmanFiniteReward_nonneg n _
    (kingmanDiversityReward_nonneg hn) h) 2)

theorem integrable_kingmanFiniteDiversityReward {n : ℕ} (hn : 2 ≤ n) :
    Integrable (kingmanFiniteReward n (kingmanDiversityReward n))
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_kingmanFiniteReward n _).aestronglyMeasurable
    (Eventually.of_forall (kingmanFiniteReward_nonneg n _
      (kingmanDiversityReward_nonneg hn)))).mp
  rw [lintegral_finiteReward n _ (kingmanDiversityReward_nonneg hn),
    lintegral_kingmanDiversityReward hn]
  exact ENNReal.ofReal_ne_top

theorem integrable_kingmanFiniteMutationReward {n : ℕ} (hn : 2 ≤ n) :
    Integrable (kingmanFiniteReward n (kingmanDiversityMutationReward n))
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_kingmanFiniteReward n _).aestronglyMeasurable
    (Eventually.of_forall (kingmanFiniteReward_nonneg n _
      (kingmanDiversityMutationReward_nonneg n)))).mp
  rw [lintegral_finiteReward n _ (kingmanDiversityMutationReward_nonneg n),
    lintegral_kingmanDiversityMutationReward (by omega : 0 < n)]
  exact ENNReal.ofReal_ne_top

theorem integrable_kingmanFiniteDiversityReward_sq {n : ℕ} (hn : 2 ≤ n) :
    Integrable (fun h => kingmanFiniteReward n (kingmanDiversityReward n) h ^ 2)
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_kingmanFiniteReward n _).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun h => sq_nonneg _)).mp
  rw [lintegral_finiteDiversity_sq hn]
  exact ENNReal.ofReal_ne_top

theorem integral_kingmanFiniteDiversityReward {n : ℕ} (hn : 2 ≤ n) :
    ∫ h, kingmanFiniteReward n (kingmanDiversityReward n) h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ = kingmanDiversityReward n ⊥ := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (kingmanFiniteReward_nonneg n _ (kingmanDiversityReward_nonneg hn)))
    (measurable_kingmanFiniteReward n _).aestronglyMeasurable,
    lintegral_finiteReward n _ (kingmanDiversityReward_nonneg hn),
    lintegral_kingmanDiversityReward hn,
    ENNReal.toReal_ofReal (kingmanDiversityReward_nonneg hn _)]

theorem integral_kingmanFiniteMutationReward {n : ℕ} (hn : 2 ≤ n) :
    ∫ h, kingmanFiniteReward n (kingmanDiversityMutationReward n) h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ = kingmanDiversityMutationPotential n ⊥ := by
  have hp : 0 ≤ kingmanDiversityMutationPotential n ⊥ := by
    rw [kingmanDiversityMutationPotential_eq_expectedCost (by omega : 0 < n)]
    exact Rhone.MarkovChain.RateChain.expectedCost_nonneg _ _
      (kingmanDiversityMutationReward_nonneg n) _
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (kingmanFiniteReward_nonneg n _
      (kingmanDiversityMutationReward_nonneg n)))
    (measurable_kingmanFiniteReward n _).aestronglyMeasurable,
    lintegral_finiteReward n _ (kingmanDiversityMutationReward_nonneg n),
    lintegral_kingmanDiversityMutationReward (by omega : 0 < n), ENNReal.toReal_ofReal hp]

theorem integral_kingmanFiniteDiversityReward_sq {n : ℕ} (hn : 2 ≤ n) :
    ∫ h, kingmanFiniteReward n (kingmanDiversityReward n) h ^ 2
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ = kingmanDiversitySquarePotential n ⊥ := by
  have hp : 0 ≤ kingmanDiversitySquarePotential n ⊥ := by
    rw [kingmanDiversitySquarePotential_eq_expectedCost (by omega : 0 < n)]
    exact Rhone.MarkovChain.RateChain.expectedCost_nonneg _ _ (fun π => by positivity) _
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun h => sq_nonneg _)
    ((measurable_kingmanFiniteReward n _).pow_const 2).aestronglyMeasurable,
    lintegral_finiteDiversity_sq hn, ENNReal.toReal_ofReal hp]
end Rhone.Coalescent
