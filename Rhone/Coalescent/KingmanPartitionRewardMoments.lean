/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanPartitionMoments
/-!
# Second moments of arbitrary nonnegative partition genealogy rewards

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset MarkovChain
open scoped ENNReal
private theorem partition_path_countdown (n : ℕ) :
    ∀ᵐ ω ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥,
      ∀ k : ℕ, (ω k).parts.card = max (n - k) (min n 1) := by
  have hL := partitionChain_lumps (α := Fin n)
  have hm := (hL.jumpChain_lumps
    (fun _ _ => partitionChain_Q_eq_zero_of_blockCount_eq)).map_pathLaw
    (⊥ : Finpartition (univ : Finset (Fin n)))
  rw [blockCount_bot] at hm
  have hf : Measurable (fun ω : ℕ → Finpartition (univ : Finset (Fin n)) =>
      fun k => blockCount (ω k)) := by fun_prop
  have hq : Measure.QuasiMeasurePreserving
      (fun ω : ℕ → Finpartition (univ : Finset (Fin n)) => fun k => blockCount (ω k))
      ((partitionChain (Fin n)).jumpChain.pathLaw ⊥)
      ((blockChain (Fintype.card (Fin n))).jumpChain.pathLaw
        (Fin.last (Fintype.card (Fin n)))) := by
    exact ⟨hf, by rw [hm]⟩
  simpa only [Fintype.card_fin, coe_blockCount] using
    hq.ae (blockChain_path_countdown (Fintype.card (Fin n)))
private noncomputable def pathCoefficient (n : ℕ)
    (c : Finpartition (univ : Finset (Fin n)) → ℝ)
    (ω : ℕ → Finpartition (univ : Finset (Fin n))) (k : ℕ) : ℝ :=
  if ω k ∈ coalescedPartitions (Fin n) then 0
  else c (ω k) / (partitionChain (Fin n)).rate (ω k)
private theorem coefficient_nonnegative (n : ℕ)
    (c : Finpartition (univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π)
    (ω : ℕ → Finpartition (univ : Finset (Fin n))) (k : ℕ) :
    0 ≤ pathCoefficient n c ω k := by
  unfold pathCoefficient
  split
  · exact le_rfl
  · exact div_nonneg (hc _) ((partitionChain (Fin n)).rate_nonneg _)
private theorem partition_cost_formula (n : ℕ)
    (c : Finpartition (univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π)
    (ω : ℕ → Finpartition (univ : Finset (Fin n))) (e : ℕ → ℝ)
    (hω : ∀ k, (ω k).parts.card = max (n - k) (min n 1)) :
    (partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n)) c (ω, e) =
      ∑ k ∈ range (n - 1), ENNReal.ofReal (pathCoefficient n c ω k) *
        ENNReal.ofReal (e k) := by
  unfold RateChain.costBefore
  rw [tsum_eq_sum (s := range (n - 1))]
  · apply sum_congr rfl
    intro k hk
    unfold pathCoefficient
    split
    · simp
    · rw [RateChain.holdTime]
      rw [show c (ω k) * (e k / (partitionChain (Fin n)).rate (ω k)) =
        (c (ω k) / (partitionChain (Fin n)).rate (ω k)) * e k by ring,
        ENNReal.ofReal_mul (div_nonneg (hc _) ((partitionChain (Fin n)).rate_nonneg _))]
  · intro k hk
    have hk' : n - 1 ≤ k := by simpa only [mem_range, not_lt] using hk
    have hv : (ω k).parts.card ≤ 1 := by have := hω k; omega
    simp [mem_coalescedPartitions.mpr hv]

theorem lintegral_partition_costBefore_sq (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π) :
    (∫⁻ h, ((partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n)) c h) ^ 2
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥) =
      ∫⁻ ω, ENNReal.ofReal
        ((∑ k : Fin (n - 1),
          if ω k.val ∈ coalescedPartitions (Fin n) then 0
          else c (ω k.val) / (partitionChain (Fin n)).rate (ω k.val)) ^ 2 +
         ∑ k : Fin (n - 1),
          (if ω k.val ∈ coalescedPartitions (Fin n) then 0
          else c (ω k.val) / (partitionChain (Fin n)).rate (ω k.val)) ^ 2)
        ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ := by
  have hae : ∀ᵐ h ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      ∀ k, (h.1 k).parts.card = max (n - k) (min n 1) :=
    Measure.quasiMeasurePreserving_fst.ae (partition_path_countdown n)
  have heq : (fun h =>
      ((partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n)) c h) ^ 2) =ᵐ[
      (partitionChain (Fin n)).jumpHoldLaw ⊥]
      (fun h => (∑ k ∈ range (n - 1),
        ENNReal.ofReal (pathCoefficient n c h.1 k) * ENNReal.ofReal (h.2 k)) ^ 2) := by
    filter_upwards [hae] with h hh
    rw [partition_cost_formula n c hc h.1 h.2 hh]
  rw [lintegral_congr_ae heq, RateChain.jumpHoldLaw]
  have hm : Measurable (fun h :
      (ℕ → Finpartition (univ : Finset (Fin n))) × (ℕ → ℝ) =>
      (∑ k ∈ range (n - 1), ENNReal.ofReal (pathCoefficient n c h.1 k) *
        ENNReal.ofReal (h.2 k)) ^ 2) := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro k hk
    have hs : Measurable (fun h :
        (ℕ → Finpartition (univ : Finset (Fin n))) × (ℕ → ℝ) => h.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have ha : Measurable (fun π : Finpartition (univ : Finset (Fin n)) =>
        if π ∈ coalescedPartitions (Fin n) then 0
        else c π / (partitionChain (Fin n)).rate π) := Measurable.of_discrete
    exact ((ha.comp hs).ennreal_ofReal).mul
      (ENNReal.measurable_ofReal.comp ((measurable_pi_apply k).comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro ω
  rw [lintegral_weighted_clock_sum_sq _ _
    (fun k hk => coefficient_nonnegative n c hc ω k)]
  simp only [pathCoefficient]
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
/-- Source: kingman1982, eq. (1.13)–(1.14). -/
theorem partition_path_terminal_coalesced (n : ℕ) :
    ∀ᵐ ω ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥,
      ω (n - 1) ∈ coalescedPartitions (Fin n) := by
  filter_upwards [partition_path_countdown n] with ω hω
  rw [mem_coalescedPartitions, hω]
  omega
end Rhone.Coalescent
