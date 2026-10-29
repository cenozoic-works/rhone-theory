/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanBlockHoldTimes
public import Rhone.Coalescent.SmcPrimeKingmanTreeLaw
public import Rhone.Coalescent.SmcPrimeKingmanLength
public import Rhone.Coalescent.SmcPrimeReferenceCutKernel

/-! # Measurability and support of Kingman root height, tree length, and waiting times -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory MarkovChain IntervalProcess
open scoped ENNReal

theorem rootHeight_measurable (N : ℕ) : Measurable (@rootHeight N) := by
  apply measurable_sigma_of_fibers
  intro m
  exact rootHeightFiber_measurable N m

theorem kingmanWaitingTimes_measurable (N : ℕ) : Measurable (kingmanWaitingTimes N) :=
  measurable_pi_iff.mpr fun j => ((measurable_pi_apply j).comp (kingmanMarks_measurable N)).snd

theorem blockHoldTimes_measurable (N : ℕ) : Measurable (blockHoldTimes N) := by
  apply measurable_pi_iff.mpr
  intro j
  have hr : Measurable fun p : (ℕ → Fin (N + 1)) × (ℕ → ℝ) => (blockChain N).rate (p.1 j.val) :=
    (Measurable.of_discrete (f := (blockChain N).rate)).comp
      ((measurable_pi_apply j.val).comp measurable_fst)
  exact ((measurable_pi_apply j.val).comp measurable_snd).div hr

theorem supported_waitingTime_nonneg (N : ℕ) (h : KingmanHistory N)
    (hs : KingmanHistorySupported N h) (j : Fin (N - 1)) : 0 ≤ kingmanWaitingTimes N h j :=
  sub_nonneg.mpr (hs.2.2 j).time_le

theorem supported_rootHeight (N : ℕ) (h : KingmanHistory N)
    (hs : KingmanHistorySupported N h) :
    ENNReal.ofReal (rootHeight (metricTreeFromHistory N h)) =
      ∑ j : Fin (N - 1), ENNReal.ofReal (kingmanWaitingTimes N h j) := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => supported_waitingTime_nonneg N h hs j]
  congr 1
  by_cases hN : 0 < N
  · have hp : (fun j : Fin N => kingmanCompletion N h j.val) = h := by
      funext j
      exact kingmanCompletion_prefix N h j.val j.isLt
    have he := metric_tree_root_height_of_pos N (kingmanCompletion N h)
      hs.completion_init hs.completion_valid hs.completion_step hN
    rw [hp] at he
    have h0 : (kingmanCompletion N h 0).1.1 = 0 := by
      rw [hs.completion_init]
      rfl
    have ht := Finset.sum_range_sub (fun k => (kingmanCompletion N h k).1.1) (N - 1)
    rw [h0, sub_zero, ← Fin.sum_univ_eq_sum_range
      (fun k => (kingmanCompletion N h (k + 1)).1.1 - (kingmanCompletion N h k).1.1)] at ht
    rw [he, ← ht]
    apply Finset.sum_congr rfl
    intro j _
    rw [kingmanCompletion_prefix N h j.val (by omega),
      kingmanCompletion_prefix N h (j.val + 1) (by omega)]
    rfl
  · have hn : N = 0 := by omega
    subst hn
    change rootHeight (treeOfList ([] : List (Branch 0))) = _
    simp [rootHeight, treeOfList]

theorem supported_treeLength (N : ℕ) (h : KingmanHistory N)
    (hs : KingmanHistorySupported N h) :
    ENNReal.ofReal (treeLength (metricTreeFromHistory N h)) =
      ∑ j : Fin (N - 1), ENNReal.ofReal (((N - j.val : ℕ) : ℝ) * kingmanWaitingTimes N h j) := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (supported_waitingTime_nonneg N h hs j)]
  congr 1
  by_cases hN : 1 ≤ N
  · rw [metric_tree_from_history_length N h hN hs]
    apply Finset.sum_congr rfl
    intro j _
    rw [(hs.1 ⟨j.val, by omega⟩).2]
    rfl
  · have hn : N = 0 := by omega
    subst hn
    change treeLength (treeOfList ([] : List (Branch 0))) = _
    simp only [treeLength, treeOfList]
    exact Finset.sum_eq_zero fun i _ => i.elim0

theorem blockChain_costBefore_det (N : ℕ) (c : Fin (N + 1) → ℝ)
    (p : (ℕ → Fin (N + 1)) × (ℕ → ℝ)) (hp : ∀ k, p.1 k = blockDet N k) :
    (blockChain N).costBefore (coalesced N) c p =
      ∑ j : Fin (N - 1), ENNReal.ofReal (c (blockDet N j.val) * blockHoldTimes N p j) := by
  unfold RateChain.costBefore
  rw [tsum_eq_sum (s := Finset.range (N - 1)), ← Fin.sum_univ_eq_sum_range (fun k =>
    if p.1 k ∈ coalesced N then (0 : ℝ≥0∞)
      else ENNReal.ofReal (c (p.1 k) * (blockChain N).holdTime p k))]
  · apply Finset.sum_congr rfl
    intro j _
    have hj : p.1 j.val ∉ coalesced N := by
      rw [hp, mem_coalesced]
      simp only [blockDet]
      omega
    rw [ite_eq_right hj, hp]
    rfl
  · intro k hk
    have hk' : p.1 k ∈ coalesced N := by
      rw [hp, mem_coalesced]
      simp only [blockDet]
      have := Finset.mem_range.not.mp hk
      omega
    rw [ite_eq_left hk']

/-- Source: kingman1982, eq. (1.12). -/
theorem kingmanTreeLaw_rootHeight_eq_tmrca (N : ℕ) :
    (kingmanTreeLaw N).map (fun T => ENNReal.ofReal (rootHeight T)) =
      ((blockChain N).jumpHoldLaw (Fin.last N)).map (tmrca N) := by
  let Φ : (Fin (N - 1) → ℝ) → ℝ≥0∞ := fun v => ∑ j, ENNReal.ofReal (v j)
  have hΦ : Measurable Φ := Finset.measurable_sum _ fun j _ =>
    ENNReal.measurable_ofReal.comp (measurable_pi_apply j)
  have hL : (kingmanTreeLaw N).map (fun T => ENNReal.ofReal (rootHeight T)) =
      ((kingmanHistoryLaw N).map (kingmanWaitingTimes N)).map Φ := by
    have hg : Measurable fun T : Tree N => ENNReal.ofReal (rootHeight T) :=
      ENNReal.measurable_ofReal.comp (rootHeight_measurable N)
    rw [kingmanTreeLaw, Measure.map_map hg (metricTreeFromHistory_measurable N),
      Measure.map_map hΦ (kingmanWaitingTimes_measurable N)]
    apply Measure.map_congr
    filter_upwards [kingmanHistoryLaw_supported N] with h hs
    exact supported_rootHeight N h hs
  have hR : ((blockChain N).jumpHoldLaw (Fin.last N)).map (tmrca N) =
      (((blockChain N).jumpHoldLaw (Fin.last N)).map (blockHoldTimes N)).map Φ := by
    rw [Measure.map_map hΦ (blockHoldTimes_measurable N)]
    apply Measure.map_congr
    rw [RateChain.jumpHoldLaw]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (blockChain_path_ae N)] with p hp
    simp only [tmrca, RateChain.timeBefore, blockChain_costBefore_det N _ p hp, one_mul,
      Function.comp_apply, Φ]
  rw [hL, hR, kingmanHistoryLaw_waitingTimes_eq_blockChain]

theorem kingmanTreeLaw_treeLength_eq_treeLength (N : ℕ) :
    (kingmanTreeLaw N).map (fun T => ENNReal.ofReal (treeLength T)) =
      ((blockChain N).jumpHoldLaw (Fin.last N)).map (Rhone.Coalescent.treeLength N) := by
  let Φ : (Fin (N - 1) → ℝ) → ℝ≥0∞ :=
    fun v => ∑ j, ENNReal.ofReal (((N - j.val : ℕ) : ℝ) * v j)
  have hΦ : Measurable Φ := Finset.measurable_sum _ fun j _ =>
    ENNReal.measurable_ofReal.comp ((measurable_pi_apply j).const_mul _)
  have hL : (kingmanTreeLaw N).map (fun T => ENNReal.ofReal (treeLength T)) =
      ((kingmanHistoryLaw N).map (kingmanWaitingTimes N)).map Φ := by
    have hg : Measurable fun T : Tree N => ENNReal.ofReal (treeLength T) :=
      ENNReal.measurable_ofReal.comp (treeLength_joint_measurable N)
    rw [kingmanTreeLaw, Measure.map_map hg (metricTreeFromHistory_measurable N),
      Measure.map_map hΦ (kingmanWaitingTimes_measurable N)]
    apply Measure.map_congr
    filter_upwards [kingmanHistoryLaw_supported N] with h hs
    exact supported_treeLength N h hs
  have hR : ((blockChain N).jumpHoldLaw (Fin.last N)).map (Rhone.Coalescent.treeLength N) =
      (((blockChain N).jumpHoldLaw (Fin.last N)).map (blockHoldTimes N)).map Φ := by
    rw [Measure.map_map hΦ (blockHoldTimes_measurable N)]
    apply Measure.map_congr
    rw [RateChain.jumpHoldLaw]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (blockChain_path_ae N)] with p hp
    simp only [Rhone.Coalescent.treeLength, blockChain_costBefore_det N _ p hp,
      Function.comp_apply, Φ]
    apply Finset.sum_congr rfl
    intro j _
    have hv : ((blockDet N j.val : Fin (N + 1)) : ℕ) = N - j.val := by
      simp only [blockDet]
      omega
    rw [hv]
  rw [hL, hR, kingmanHistoryLaw_waitingTimes_eq_blockChain]

end Rhone.Coalescent.SmcPrime
