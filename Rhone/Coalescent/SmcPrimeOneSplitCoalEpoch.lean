/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeOldTreeCoalExposure
public import Rhone.Coalescent.SmcPrimeOneSplitExposureSupport
public import Rhone.Coalescent.SmcPrimeOneSplitCount

/-! # Attachment rate and pair-exposure integrals over the epochs of the extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport
theorem extractionRun_attachmentRate_epoch (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (n : ℕ) (hn : n < N + 1) (q : ℝ)
    (hlo : (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.1 ≤ q)
    (hhi : q < (h ⟨n + 1, Finset.mem_Iic.mpr (by omega)⟩).1.1) :
    attachmentRate (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) q =
      ((extractionRun N h n).old.1.2.2.1 : ℝ) := by
  let z := extractionRun N h n
  let η := extractOneSplitSkeleton N h
  let ω := kingmanCompletion N η.1
  change attachmentRate (metricTreeFromHistory N η.1) q = (z.old.1.2.2.1 : ℝ)
  have hp := extractionRun_history_prefix N h hs n (by omega)
  have hk := extractOneSplitSkeleton_history_supported N h hs
  have he : (fun j : Fin N => ω j.val) = η.1 := by
    funext j
    exact kingmanCompletion_prefix N η.1 j.val j.isLt
  have hcur : η.1 ⟨z.mergers, hp.bound⟩ = z.old :=
    extractionRun_final_old_record N h hs n (by omega)
  have hr := metric_tree_root_height_of_pos N ω hk.completion_init
    hk.completion_valid hk.completion_step hs.sample_pos
  rw [he] at hr
  by_cases hm : z.mergers < N - 1
  · obtain ⟨hl, hu⟩ := extractionRun_old_clock_interval N h hs n hn hm q hlo hhi
    have hl' : (ω z.mergers).1.1 ≤ q := by
      dsimp only [ω]
      rwa [kingmanCompletion_prefix N η.1 z.mergers hp.bound]
    have hu' : q < (ω (z.mergers + 1)).1.1 := by
      dsimp only [ω]
      rwa [kingmanCompletion_prefix N η.1 (z.mergers + 1) (by omega)]
    have hmono : Monotone (fun k => (ω k).1.1) :=
      monotone_nat_of_le_succ (fun k => (hk.completion_step k).time_le)
    have hqr : q < rootHeight (metricTreeFromHistory N η.1) := by
      rw [hr]
      exact hu'.trans_le (hmono (by omega))
    have ha := kingman_active_branch_card N ω hk.completion_init hk.completion_valid
      hk.completion_step z.mergers hm q hl' hu'
    rw [he] at ha
    dsimp only [ω] at ha
    rw [kingmanCompletion_prefix N η.1 z.mergers hp.bound, hcur] at ha
    simp only [attachmentRate, not_le.mpr hqr, ite_false, ha]
  · have hm' : z.mergers = N - 1 := by
      have hb : z.mergers < N := hp.bound
      omega
    have hqr : rootHeight (metricTreeFromHistory N η.1) ≤ q := by
      rw [hr, ← hm']
      dsimp only [ω]
      rw [kingmanCompletion_prefix N η.1 z.mergers hp.bound, hcur]
      exact (extractionRun_clock_le N h hs n (by omega)).trans hlo
    have hc : z.old.1.2.2.1 = 1 := by
      have hh := (hp.records ⟨z.mergers, hp.bound⟩ le_rfl).2
      rw [hp.current] at hh
      change z.old.1.2.2.1 = N - z.mergers at hh
      have := hs.sample_pos
      omega
    simp only [attachmentRate, hqr, ite_true, hc, Nat.cast_one]

theorem extractionRun_old_pair_integral (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (n : Fin (N + 1)) :
    (∫ q in (h ⟨n.val, Finset.mem_Iic.mpr (by omega)⟩).1.1..
      (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1,
      oldTreeCoalRate (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) q) =
    ((extractionRun N h n.val).old.1.2.2.1 : ℝ) *
      (((extractionRun N h n.val).old.1.2.2.1 : ℝ) - 1) / 2 *
      ((h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1 -
        (h ⟨n.val, Finset.mem_Iic.mpr (by omega)⟩).1.1) := by
  rw [mul_comm _ ((h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1 -
    (h ⟨n.val, Finset.mem_Iic.mpr (by omega)⟩).1.1), ← smul_eq_mul,
    ← intervalIntegral.integral_const]
  apply intervalIntegral.integral_congr_Ioo_of_le (hs.clock_lt n).le
  intro q hq
  rw [oldTreeCoalRate, extractionRun_attachmentRate_epoch N h hs n.val n.isLt q
    hq.1.le hq.2]

theorem OneSplitARGWitness.cut_time {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) :
    (extractOneSplitSkeleton N h).2.2.1 =
      (h ⟨w.cutStep.val + 1, Finset.mem_Iic.mpr w.cutStep.isLt⟩).1.1 := by
  change (extractionRun N h (N + 1)).cut.2.1 = _
  rw [w.cut_field, extractionPrefixExtension_prefix N h (w.cutStep.val + 1) w.cutStep.isLt]

theorem OneSplitARGWitness.attach_time {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) :
    (extractOneSplitSkeleton N h).2.2.2.2.1 =
      (h ⟨w.attachStep + 1, Finset.mem_Iic.mpr w.attach_bound⟩).1.1 := by
  rw [w.attach_field, extractionPrefixExtension_prefix N h (w.attachStep + 1) w.attach_bound]

theorem OneSplitARGWitness.detached_before {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) (n : ℕ) (hn : n ≤ w.cutStep.val) :
    (extractionRun N h n).detached = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [extractionRun_succ N h n (by have := w.cutStep.isLt; omega)]
    apply (extractionStep_attachment_stable _ _ _ (ih (by omega)) _).1
    have he := w.other_event n (by omega)
    rwa [extractionPrefixExtension_prefix N h (n + 1) (by have := w.cutStep.isLt; omega)] at he

theorem OneSplitARGWitness.detached_after {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) (n : ℕ) (hn : n ≤ N + 1)
    (han : w.attachStep + 1 ≤ n) : (extractionRun N h n).detached = none := by
  obtain ⟨_, _, hd⟩ := w.detached_present
  exact (extractionRun_attachment_stable N h (w.attachStep + 1) hd
    (fun m hm => w.other_event m (by have := w.cut_before_attach; omega)) n hn han).1

theorem extractionRun_detached_rate_epoch (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (w : OneSplitARGWitness N h)
    (n : ℕ) (hn : n < N + 1) (q : ℝ)
    (hlo : (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩).1.1 < q)
    (hhi : q < (h ⟨n + 1, Finset.mem_Iic.mpr (by omega)⟩).1.1) :
    detachedAttachmentRate (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
      (extractOneSplitSkeleton N h).2.2.1 (extractOneSplitSkeleton N h).2.2.2.2.1 q =
      ((extractionRun N h n).old.1.2.2.1 : ℝ) *
        (extractionRun N h n).detached.toFinset.card := by
  classical
  have ha := extractionRun_attachmentRate_epoch N h hs n hn q hlo.le hhi
  simp only [detachedAttachmentRate, Set.indicator, Set.mem_Ioo, w.cut_time, w.attach_time]
  by_cases hc : w.cutStep.val + 1 ≤ n
  · by_cases hat : n ≤ w.attachStep
    · obtain ⟨a, hd⟩ := w.detached_between n hc hat
      have htq := (hs.clock_mono (w.cutStep.val + 1) n hc (by omega)).trans_lt hlo
      have hqU := hhi.trans_le
        (hs.clock_mono (n + 1) (w.attachStep + 1) (by omega) w.attach_bound)
      simp only [htq, hqU, and_self, ite_true, ha, hd,
        Option.toFinset_some, Finset.card_singleton, Nat.cast_one, mul_one]
    · have hd := w.detached_after n (by omega) (by omega)
      have hUq := (hs.clock_mono (w.attachStep + 1) n (by omega) (by omega)).trans_lt hlo
      simp only [not_lt.mpr hUq.le, and_false, ite_false, hd,
        Option.toFinset_none, Finset.card_empty, Nat.cast_zero, mul_zero]
  · have hd := w.detached_before n (by omega)
    have hqt := hhi.trans_le
      (hs.clock_mono (n + 1) (w.cutStep.val + 1) (by omega) w.cutStep.isLt)
    simp only [not_lt.mpr hqt.le, false_and, ite_false, hd,
      Option.toFinset_none, Finset.card_empty, Nat.cast_zero, mul_zero]

theorem extractionRun_detached_integral (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (w : OneSplitARGWitness N h)
    (n : Fin (N + 1)) :
    (∫ q in (h ⟨n.val, Finset.mem_Iic.mpr (by omega)⟩).1.1..
      (h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1,
      detachedAttachmentRate (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
        (extractOneSplitSkeleton N h).2.2.1 (extractOneSplitSkeleton N h).2.2.2.2.1 q) =
    (((extractionRun N h n.val).old.1.2.2.1 : ℝ) *
      (extractionRun N h n.val).detached.toFinset.card) *
      ((h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1 -
        (h ⟨n.val, Finset.mem_Iic.mpr (by omega)⟩).1.1) := by
  rw [mul_comm _ ((h ⟨n.val + 1, Finset.mem_Iic.mpr n.isLt⟩).1.1 -
    (h ⟨n.val, Finset.mem_Iic.mpr (by omega)⟩).1.1), ← smul_eq_mul,
    ← intervalIntegral.integral_const]
  apply intervalIntegral.integral_congr_Ioo_of_le (hs.clock_lt n).le
  intro q hq
  exact extractionRun_detached_rate_epoch N h hs w n.val n.isLt q hq.1 hq.2
end Rhone.Coalescent.SmcPrime
