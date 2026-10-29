/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitPhaseClades

/-! # Active clades of the right sample over the epochs of the extraction -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem OneSplitPrefixSupported.epoch_before_event {N : ℕ} {h : ARGPrefix (N + 1)}
    (hs : OneSplitPrefixSupported N h) (n : ℕ) (hn : n < N + 1) (y : ℝ)
    (hlo : (extractionPrefixExtension N h n).1.1 ≤ y)
    (hhi : y < (extractionPrefixExtension N h (n + 1)).1.1)
    (m : ℕ) (hm : m < N + 1) :
    y < (extractionPrefixExtension N h (m + 1)).1.1 ↔ n ≤ m := by
  rw [extractionPrefixExtension_prefix N h n hn.le] at hlo
  rw [extractionPrefixExtension_prefix N h (n + 1) hn] at hhi
  rw [extractionPrefixExtension_prefix N h (m + 1) hm]
  constructor
  · intro hy
    by_contra hnm
    have he := hs.clock_mono (m + 1) n (by omega) hn.le
    exact (not_lt_of_ge (he.trans hlo)) hy
  · intro hnm
    exact hhi.trans_le (hs.clock_mono (n + 1) (m + 1) (by omega) hm)

theorem extraction_timeClades_epoch_labels (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (n : ℕ) (hn : n < N + 1) (y : ℝ)
    (hlo : (extractionPrefixExtension N h n).1.1 ≤ y)
    (hhi : y < (extractionPrefixExtension N h (n + 1)).1.1) :
    timeClades (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) y =
      Finset.univ.image (fun j =>
        extractionClade (fun a => ancestorLabel N (extractionPrefixExtension N h)
          leftBoundaryProbe a n)
          (ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j n)) := by
  rw [extractionPrefixExtension_prefix N h n hn.le] at hlo
  rw [extractionPrefixExtension_prefix N h (n + 1) hn] at hhi
  rw [extraction_timeClades_epoch N h hs n hn y hlo hhi]
  congr 1
  funext j
  have hf : (extractionRun N h n).argLabels =
      fun a => ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe a n :=
    funext (extractionRun_argLabels N h n hn.le)
  rw [hf]

theorem extractOneSplitSkeleton_right_active_clade (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (q : GenomicProbe)
    (hq : (extractOneSplitSkeleton N h).2.2.2.1 ≤ (q.val : ℝ))
    (n : ℕ) (hn : n < N + 1) (y : ℝ)
    (hlo : (extractionPrefixExtension N h n).1.1 ≤ y)
    (hhi : y < (extractionPrefixExtension N h (n + 1)).1.1)
    (i : Fin (oneSplitPostTree (extractOneSplitSkeleton N h)).1)
    (hi : i ∈ activeBranches (oneSplitPostTree (extractOneSplitSkeleton N h)) y) :
    ∃ a, ((oneSplitPostTree (extractOneSplitSkeleton N h)).2 i).1 =
      extractionClade (fun j => ancestorLabel N (extractionPrefixExtension N h) q j n) a := by
  classical
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  have hcoords := extractOneSplitSkeleton_cut_coordinates N h w.cutStep w.cutIndex
    w.cutPosition w.cut_event w.other_event
  have hqx : w.cutPosition ≤ (q.val : ℝ) := by rwa [hcoords.2] at hq
  have hcutphase := hs.epoch_before_event n hn y hlo hhi w.cutStep.val w.cutStep.isLt
  have hattphase := hs.epoch_before_event n hn y hlo hhi w.attachStep w.attach_bound
  rw [← hcoords.1] at hcutphase
  have hattclock : (extractOneSplitSkeleton N h).2.2.2.2.1 =
      (extractionPrefixExtension N h (w.attachStep + 1)).1.1 := congrArg Prod.fst w.attach_field
  rw [← hattclock] at hattphase
  have hold := extraction_timeClades_epoch_labels N h hs n hn y hlo hhi
  obtain ⟨_, hta, hroot, _, _, _⟩ := extractOneSplitSkeleton_cut_geometry N h hs
  have hform := regraft_active_clade_form
    (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
    (rebuildCutClade (extractOneSplitSkeleton N h)) (extractOneSplitSkeleton N h).2.2.2.2.2
    (extractOneSplitSkeleton N h).2.2.1 (extractOneSplitSkeleton N h).2.2.2.2.1 y
    (metric_tree_from_history_normalized N _) hroot hta
  rw [← oneSplitPostTree_regraft] at hform
  rcases hform i hi with ⟨hyt, hcl⟩ | ⟨hty, hya, hcl⟩ | ⟨hay, c, hc, hcl⟩
  · rw [hold] at hcl
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hcl
    refine ⟨ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j n, ?_⟩
    rw [← hj]
    congr 1
    funext a
    exact (w.right_before q a n (hcutphase.mp hyt)).symm
  · have hcn : w.cutStep.val + 1 ≤ n := by
      have hnot : ¬ n ≤ w.cutStep.val := fun he => (not_lt_of_ge hty) (hcutphase.mpr he)
      omega
    have hnl : n ≤ w.attachStep := hattphase.mp hya
    obtain ⟨a, ha, hleft⟩ := w.right_middle hs q hqx n hcn hnl
    rcases hcl with hc | ⟨c, hc, he⟩
    · exact ⟨a, hc.trans ha.symm⟩
    · rw [hold] at hc
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
      exact ⟨ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j n,
        he.trans ((congrArg (fun C => C \ rebuildCutClade (extractOneSplitSkeleton N h))
          hj.symm).trans (hleft j).symm)⟩
  · have hln : w.attachStep + 1 ≤ n := by
      have hnot : ¬ n ≤ w.attachStep := fun he => (not_lt_of_ge hay) (hattphase.mpr he)
      omega
    rw [hold] at hc
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
    refine ⟨ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j n, ?_⟩
    rw [w.right_after hs q hqx n hln]
    exact hcl.trans (congrArg (regraftClade (rebuildCutClade (extractOneSplitSkeleton N h))
      (extractOneSplitSkeleton N h).2.2.2.2.2) hj.symm)

end Rhone.Coalescent.SmcPrime
