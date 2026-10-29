/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.KingmanPartitionRewardMoments

/-!
# Finite genealogy reward histories for Poisson mutation marking

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset MarkovChain

/-- Source: kingman1982, eq. (1.14). -/
theorem partition_path_countdown_general (n : ℕ) :
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

theorem partition_costBefore_eq_finite_clamped_sum (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π) :
    ∀ᵐ h ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      (partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n)) c h =
      ENNReal.ofReal (∑ k : Fin (n - 1),
        if h.1 k.val ∈ coalescedPartitions (Fin n) then 0
        else c (h.1 k.val) * max 0 ((partitionChain (Fin n)).holdTime h k.val)) := by
  have hae : ∀ᵐ h ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      ∀ k : ℕ, (h.1 k).parts.card = max (n - k) (min n 1) :=
    Measure.quasiMeasurePreserving_fst.ae (partition_path_countdown_general n)
  filter_upwards [hae] with h hh
  unfold RateChain.costBefore
  rw [tsum_eq_sum (s := range (n - 1))]
  · rw [← Fin.sum_univ_eq_sum_range]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by
      split_ifs <;> first | exact le_rfl | exact mul_nonneg (hc _) (le_max_left _ _))]
    apply sum_congr rfl
    intro k _
    split_ifs with hk
    · simp
    · by_cases ht : 0 ≤ (partitionChain (Fin n)).holdTime h k.val
      · rw [max_eq_right ht]
      · have hct : c (h.1 k.val) * (partitionChain (Fin n)).holdTime h k.val ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (hc _) (le_of_not_ge ht)
        rw [max_eq_left (le_of_not_ge ht), mul_zero, ENNReal.ofReal_zero,
          ENNReal.ofReal_eq_zero.mpr hct]
  · intro k hk
    have hk' : n - 1 ≤ k := by simpa only [mem_range, not_lt] using hk
    have hv : (h.1 k).parts.card ≤ 1 := by have := hh k; omega
    simp [mem_coalescedPartitions.mpr hv]

end Rhone.Coalescent
