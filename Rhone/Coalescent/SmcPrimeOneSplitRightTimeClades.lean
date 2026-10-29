/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightFibreForm
public import Rhone.Coalescent.SmcPrimeTimeCladesFibres

/-! # Time clades of the right tree over the epochs of the extraction -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem extractOneSplitSkeleton_right_timeClades (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (q : GenomicProbe)
    (hq : (extractOneSplitSkeleton N h).2.2.2.1 ≤ (q.val : ℝ))
    (n : ℕ) (hn : n < N + 1) (y : ℝ)
    (hlo : (extractionPrefixExtension N h n).1.1 ≤ y)
    (hhi : y < (extractionPrefixExtension N h (n + 1)).1.1) :
    timeClades (oneSplitPostTree (extractOneSplitSkeleton N h)) y =
      Finset.univ.image (fun j =>
        extractionClade (fun a => ancestorLabel N (extractionPrefixExtension N h) q a n)
          (ancestorLabel N (extractionPrefixExtension N h) q j n)) := by
  have hy0 : 0 ≤ y := by
    rw [extractionPrefixExtension_prefix N h n hn.le] at hlo
    exact (hs.clock_nonneg _).trans hlo
  have hpost := extractOneSplitSkeleton_post_geometry N h hs
  apply timeClades_eq_sample_fibres hs.sample_pos _ hpost.2.2.1 y hy0
    (fun j => ancestorLabel N (extractionPrefixExtension N h) q j n)
  · exact extractOneSplitSkeleton_right_active_clade N h hs q hq n hn y hlo hhi
  · intro j hj
    have hform := extractOneSplitSkeleton_right_fibre_form N h hs q hq n hn y hlo hhi j
    have hc0 : extractionClade (fun a => ancestorLabel N (extractionPrefixExtension N h) q a n)
        (ancestorLabel N (extractionPrefixExtension N h) q j n) ≠ ∅ := by
      apply Finset.nonempty_iff_ne_empty.mp
      exact ⟨j, by simp [extractionClade]⟩
    have hk := extractOneSplitSkeleton_history_supported N h hs
    have hchron := metric_tree_from_history_chronology N _ hs.sample_pos hk
    obtain ⟨ht, hta, _, _, _, _⟩ := extractOneSplitSkeleton_cut_geometry N h hs
    have htarget := (hchron.1 _ (ht.trans hta)).1 _
      (extractOneSplitSkeleton_target_timeClades N h hs)
    have ha := regraft_clade_at_active _ _ _ _ _ _ _ htarget hc0 hj hform
    rw [← oneSplitPostTree_regraft] at ha
    exact ha

end Rhone.Coalescent.SmcPrime
