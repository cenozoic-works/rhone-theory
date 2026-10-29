/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanPartition
public import Rhone.Coalescent.KingmanVariances
/-!
# Partition genealogy second moments and variances transferred in law

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset MarkovChain
open scoped ENNReal
private theorem measurable_rate_cost {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (R : RateChain S) (A : Finset S) (c : S → ℝ) : Measurable (R.costBefore A c) := by
  unfold RateChain.costBefore RateChain.holdTime
  apply Measurable.tsum
  intro k
  have hstate : Measurable (fun p : (ℕ → S) × (ℕ → ℝ) => p.1 k) :=
    (measurable_pi_apply k).comp measurable_fst
  have hset := (MeasurableSet.of_discrete (s := {x : S | x ∈ A})).preimage hstate
  have hc : Measurable c := Measurable.of_discrete
  have hr : Measurable R.rate := Measurable.of_discrete
  exact measurable_const.ite hset
    (((hc.comp hstate).mul
      (((measurable_pi_apply k).comp measurable_snd).div (hr.comp hstate))).ennreal_ofReal)
theorem lintegral_partitionTmrca_sq (α : Type*) [Fintype α] [DecidableEq α] :
    ∫⁻ p, (partitionTmrca p) ^ 2 ∂(partitionChain α).jumpHoldLaw ⊥ =
      ENNReal.ofReal ((expTMRCA (Fintype.card α) : ℝ) ^ 2 +
        (varTMRCA (Fintype.card α) : ℝ)) := by
  have hp : Measurable (@partitionTmrca α _ _) :=
    measurable_rate_cost (partitionChain α) (coalescedPartitions α) (fun _ => 1)
  have hb : Measurable (tmrca (Fintype.card α)) :=
    measurable_rate_cost (blockChain (Fintype.card α)) (coalesced (Fintype.card α)) (fun _ => 1)
  rw [← lintegral_map (f := fun x : ℝ≥0∞ => x ^ 2) (by fun_prop) hp,
    map_partitionTmrca,
    lintegral_map (f := fun x : ℝ≥0∞ => x ^ 2) (by fun_prop) hb, lintegral_tmrca_sq]
theorem lintegral_partitionTreeLength_sq (α : Type*) [Fintype α] [DecidableEq α] :
    ∫⁻ p, (partitionTreeLength p) ^ 2 ∂(partitionChain α).jumpHoldLaw ⊥ =
      ENNReal.ofReal ((expLength (Fintype.card α) : ℝ) ^ 2 +
        (varLength (Fintype.card α) : ℝ)) := by
  have hp : Measurable (@partitionTreeLength α _ _) :=
    measurable_rate_cost (partitionChain α) (coalescedPartitions α) (fun π => (π.parts.card : ℝ))
  have hb : Measurable (treeLength (Fintype.card α)) :=
    measurable_rate_cost (blockChain (Fintype.card α)) (coalesced (Fintype.card α)) (fun k => k)
  rw [← lintegral_map (f := fun x : ℝ≥0∞ => x ^ 2) (by fun_prop) hp,
    map_partitionTreeLength,
    lintegral_map (f := fun x : ℝ≥0∞ => x ^ 2) (by fun_prop) hb, lintegral_treeLength_sq]
theorem variance_partitionTmrca (α : Type*) [Fintype α] [DecidableEq α] :
    ProbabilityTheory.variance (fun p => (partitionTmrca p).toReal)
      ((partitionChain α).jumpHoldLaw ⊥) = (varTMRCA (Fintype.card α) : ℝ) := by
  have hp : Measurable (@partitionTmrca α _ _) :=
    measurable_rate_cost (partitionChain α) (coalescedPartitions α) (fun _ => 1)
  have hb : Measurable (tmrca (Fintype.card α)) :=
    measurable_rate_cost (blockChain (Fintype.card α)) (coalesced (Fintype.card α)) (fun _ => 1)
  have hpv := variance_map (X := ENNReal.toReal) ENNReal.measurable_toReal.aemeasurable
    (μ := (partitionChain α).jumpHoldLaw ⊥) hp.aemeasurable
  have hbv := variance_map (X := ENNReal.toReal) ENNReal.measurable_toReal.aemeasurable
    (μ := (blockChain (Fintype.card α)).jumpHoldLaw (Fin.last (Fintype.card α))) hb.aemeasurable
  change variance (ENNReal.toReal ∘ partitionTmrca) _ = _
  rw [← hpv, map_partitionTmrca, hbv]
  exact variance_tmrca _
theorem variance_partitionTreeLength (α : Type*) [Fintype α] [DecidableEq α] :
    ProbabilityTheory.variance (fun p => (partitionTreeLength p).toReal)
      ((partitionChain α).jumpHoldLaw ⊥) = (varLength (Fintype.card α) : ℝ) := by
  have hp : Measurable (@partitionTreeLength α _ _) :=
    measurable_rate_cost (partitionChain α) (coalescedPartitions α) (fun π => (π.parts.card : ℝ))
  have hb : Measurable (treeLength (Fintype.card α)) :=
    measurable_rate_cost (blockChain (Fintype.card α)) (coalesced (Fintype.card α)) (fun k => k)
  have hpv := variance_map (X := ENNReal.toReal) ENNReal.measurable_toReal.aemeasurable
    (μ := (partitionChain α).jumpHoldLaw ⊥) hp.aemeasurable
  have hbv := variance_map (X := ENNReal.toReal) ENNReal.measurable_toReal.aemeasurable
    (μ := (blockChain (Fintype.card α)).jumpHoldLaw (Fin.last (Fintype.card α))) hb.aemeasurable
  change variance (ENNReal.toReal ∘ partitionTreeLength) _ = _
  rw [← hpv, map_partitionTreeLength, hbv]
  exact variance_treeLength _
end Rhone.Coalescent
