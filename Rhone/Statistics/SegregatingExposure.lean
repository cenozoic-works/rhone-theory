/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.TajimaFiniteMoments
public import Rhone.Coalescent.KingmanPartitionMoments

/-!
# Finite total branch exposure inherits the existing partition length moments

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7); watterson1975, p. 258, eq. (1.4a)–(1.5a), p.
267; durrett2008, eq. (1.21). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Filter

private theorem length_nonneg (n : ℕ) : 0 ≤ (expLength n : ℝ) := by
  have hq : (0 : ℚ) ≤ expLength n := by
    unfold expLength holdingTime
    exact sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k)
      (div_nonneg (by norm_num) (coalRate_nonneg k))
  exact_mod_cast hq

private theorem length_variance_nonneg (n : ℕ) : 0 ≤ (varLength n : ℝ) := by
  have hq : (0 : ℚ) ≤ varLength n := by
    unfold varLength
    exact sum_nonneg fun k _ => sq_nonneg ((k : ℚ) * holdingTime k)
  exact_mod_cast hq

theorem lintegral_kingmanFiniteLength (n : ℕ) :
    (∫⁻ h, ENNReal.ofReal (kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h)
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥) = ENNReal.ofReal (expLength n : ℝ) := by
  have hm := lintegral_partitionTreeLength (Fin n)
  simp only [Fintype.card_fin] at hm
  rw [← hm]
  apply lintegral_congr_ae
  filter_upwards [partition_costBefore_eq_finite_clamped_sum n
    (fun π => (π.parts.card : ℝ)) (fun π => Nat.cast_nonneg π.parts.card)] with h hh
  simpa only [kingmanFiniteReward, partitionTreeLength] using hh.symm

theorem lintegral_kingmanFiniteLength_sq (n : ℕ) :
    (∫⁻ h, ENNReal.ofReal (kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h ^ 2)
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥) =
      ENNReal.ofReal ((expLength n : ℝ) ^ 2 + (varLength n : ℝ)) := by
  have hm := lintegral_partitionTreeLength_sq (Fin n)
  simp only [Fintype.card_fin] at hm
  rw [← hm]
  apply lintegral_congr_ae
  filter_upwards [partition_costBefore_eq_finite_clamped_sum n
    (fun π => (π.parts.card : ℝ)) (fun π => Nat.cast_nonneg π.parts.card)] with h hh
  change ENNReal.ofReal (kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h ^ 2) =
    ((partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n))
      (fun π => (π.parts.card : ℝ)) h) ^ 2
  rw [hh]
  exact ENNReal.ofReal_pow (kingmanFiniteReward_nonneg n _
    (fun π => Nat.cast_nonneg π.parts.card) h) 2

theorem integrable_kingmanFiniteLength (n : ℕ) :
    Integrable (kingmanFiniteReward n (fun π => (π.parts.card : ℝ)))
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_kingmanFiniteReward n _).aestronglyMeasurable
    (Eventually.of_forall (kingmanFiniteReward_nonneg n _
      (fun π => Nat.cast_nonneg π.parts.card)))).mp
  rw [lintegral_kingmanFiniteLength n]
  exact ENNReal.ofReal_ne_top

theorem integrable_kingmanFiniteLength_sq (n : ℕ) :
    Integrable (fun h => kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h ^ 2)
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_kingmanFiniteReward n _).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun h => sq_nonneg _)).mp
  rw [lintegral_kingmanFiniteLength_sq n]
  exact ENNReal.ofReal_ne_top

theorem integral_kingmanFiniteLength (n : ℕ) :
    (∫ h, kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥) = (expLength n : ℝ) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (kingmanFiniteReward_nonneg n _
      (fun π => Nat.cast_nonneg π.parts.card)))
    (measurable_kingmanFiniteReward n _).aestronglyMeasurable,
    lintegral_kingmanFiniteLength n, ENNReal.toReal_ofReal (length_nonneg n)]

theorem integral_kingmanFiniteLength_sq (n : ℕ) :
    (∫ h, kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h ^ 2
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥) =
      (expLength n : ℝ) ^ 2 + (varLength n : ℝ) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun h => sq_nonneg _)
    ((measurable_kingmanFiniteReward n _).pow_const 2).aestronglyMeasurable,
    lintegral_kingmanFiniteLength_sq n,
    ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _) (length_variance_nonneg n))]

end Rhone.Statistics
