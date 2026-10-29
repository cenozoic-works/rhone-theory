/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitTraceChronology
public import Rhone.Coalescent.SmcPrimeOneSplitExtractedGeometry
public import Rhone.Coalescent.SmcPrimeIndexedCutFlat
public import Rhone.Coalescent.SmcPrimeAttachmentFlatLaw

/-! # Cut density and attachment target rate of the extracted one-split skeleton -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem pairBirthTime_ne_of_clocks (ω : EventPath) (k a : ℕ) (t : ℝ)
    (hz : (0 : ℝ) ≠ t) (ht : ∀ j < k, (ω (j + 1)).1.1 ≠ t) :
    pairBirthTime ω k a ≠ t := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    have hp := ih (fun j hj => ht j (by omega))
    unfold pairBirthTime
    split
    · split
      · exact ht k (by omega)
      · exact hp
    · exact hp

theorem extractOneSplitSkeleton_branch_birth_lt (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h)
    (b : Fin (metricTreeFromHistory N (extractOneSplitSkeleton N h).1).1)
    (hb : b ∈ activeBranches (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
      (extractOneSplitSkeleton N h).2.2.1) :
    ((metricTreeFromHistory N (extractOneSplitSkeleton N h).1).2 b).2.1 <
      (extractOneSplitSkeleton N h).2.2.1 := by
  let η := extractOneSplitSkeleton N h
  let ω := kingmanCompletion N η.1
  have hk := extractOneSplitSkeleton_history_supported N h hs
  have he : (fun j : Fin N => ω j.val) = η.1 := by
    funext j
    exact kingmanCompletion_prefix N η.1 j.val j.isLt
  obtain ⟨k, r, hchild⟩ := metric_tree_branch_from_child N η.1 b
  obtain ⟨a, _, hdata⟩ := kingman_child_data N ω hk.completion_init hk.completion_valid
    hk.completion_step k r
  rw [he] at hdata
  have htpos : 0 < η.2.2.1 := by
    obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
    have ht := (extractOneSplitSkeleton_cut_coordinates N h w.cutStep w.cutIndex
      w.cutPosition w.cut_event w.other_event).1
    change η.2.2.1 = _ at ht
    rw [ht, extractionPrefixExtension_prefix N h (w.cutStep.val + 1) w.cutStep.isLt]
    exact (hs.clock_nonneg _).trans_lt (hs.clock_lt w.cutStep)
  have hne : pairBirthTime ω k.val a ≠ η.2.2.1 := by
    apply pairBirthTime_ne_of_clocks ω k.val a η.2.2.1 (ne_of_lt htpos)
    intro j hj
    have hjN : j < N - 1 := hj.trans k.isLt
    have hclock : (ω (j + 1)).1.1 = rebuildEventTime η (.inl ⟨j, hjN⟩) := by
      simp only [ω, kingmanCompletion_prefix N η.1 (j + 1) (by omega), rebuildEventTime]
    rw [hclock]
    intro hx
    have hx' : rebuildEventTime η (.inl ⟨j, hjN⟩) = rebuildEventTime η (.inr false) := hx
    have hi := extractionRebuildEventTime_injective N h hs hx'
    cases hi
  have hlo := (Finset.mem_filter.mp hb).2.2.1
  have helo : ((metricTreeFromHistory N η.1).2 b).2.1 = pairBirthTime ω k.val a := by
    rw [hchild, hdata]
  rw [helo] at hlo ⊢
  exact lt_of_le_of_ne hlo hne

theorem extractOneSplitSkeleton_indexedCutDensity (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    indexedCutDensity (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
      ((extractOneSplitSkeleton N h).2.1, (extractOneSplitSkeleton N h).2.2.1) = 1 := by
  classical
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  have hi := w.cut_index
  rw [extractionPrefixExtension_prefix N h w.cutStep.val w.cutStep.isLt.le] at hi
  have hev := w.cut_event
  rw [extractionPrefixExtension_prefix N h (w.cutStep.val + 1) w.cutStep.isLt] at hev
  obtain ⟨b, hb, hidx, _⟩ := extractOneSplitSkeleton_cut_branch N h hs w.cutStep
    ⟨w.cutIndex, hi⟩ w.cutPosition hev
  have hlo := extractOneSplitSkeleton_branch_birth_lt N h hs b hb
  have hp := (Finset.mem_filter.mp hb).2
  have hc : ((metricTreeFromHistory N (extractOneSplitSkeleton N h).1).2 b).1 ≠ ∅ ∧
      ((metricTreeFromHistory N (extractOneSplitSkeleton N h).1).2 b).1 ≠ Finset.univ := by
    by_contra hz
    have hn := not_and_or.mp hz
    rcases hn with he | he <;> simp [branchLength, Classical.not_not.mp he] at hp
  rw [hidx]
  simp only [indexedCutDensity, dite_eq_left b.isLt]
  exact ite_eq_left ⟨hc.1, hc.2, hlo, hp.2.2⟩

theorem extractOneSplitSkeleton_attachmentTargetRate (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    attachmentTargetRate (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
      (extractOneSplitSkeleton N h).2.2.2.2.1 (extractOneSplitSkeleton N h).2.2.2.2.2 = 1 := by
  have hk := extractOneSplitSkeleton_history_supported N h hs
  obtain ⟨ht, hta, _, _, _, _⟩ := extractOneSplitSkeleton_cut_geometry N h hs
  rw [attachmentTargetRate_of_active_unique _
    (metric_tree_from_history_active_unique N _ hs.sample_pos hk) _ (ht.trans hta),
    ite_eq_left (extractOneSplitSkeleton_target_timeClades N h hs)]

end Rhone.Coalescent.SmcPrime
