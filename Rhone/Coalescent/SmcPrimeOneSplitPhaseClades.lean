/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtractedGeometry

/-! # Right sample fibres in each phase of the extracted regraft -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem OneSplitARGWitness.detached_between {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) (n : ℕ)
    (hcn : w.cutStep.val + 1 ≤ n) (hnl : n ≤ w.attachStep) :
    ∃ a, (extractionRun N h n).detached = some a := by
  cases hd : (extractionRun N h n).detached with
  | none =>
    have hstable := extractionRun_attachment_stable N h n hd
      (fun m hm => w.other_event m (by omega)) w.attachStep w.attach_bound.le hnl
    obtain ⟨a, ha, _⟩ := w.detached_present
    rw [ha] at hstable
    cases hstable.1
  | some a => exact ⟨a, rfl⟩

theorem OneSplitARGWitness.right_before {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) (q : GenomicProbe) (j : Fin N) (n : ℕ)
    (hn : n ≤ w.cutStep.val) :
    ancestorLabel N (extractionPrefixExtension N h) q j n =
      ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j n :=
  ancestorLabel_no_split_prefix N _ n (fun l hl => w.other_event l (by omega)) q
    leftBoundaryProbe j

theorem OneSplitARGWitness.right_middle {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) (hs : OneSplitPrefixSupported N h)
    (q : GenomicProbe) (hq : w.cutPosition ≤ (q.val : ℝ)) (n : ℕ)
    (hcn : w.cutStep.val + 1 ≤ n) (hnl : n ≤ w.attachStep) :
    let ω := extractionPrefixExtension N h
    ∃ a, extractionClade (fun j => ancestorLabel N ω q j n) a =
        rebuildCutClade (extractOneSplitSkeleton N h) ∧
      ∀ j, extractionClade (fun j => ancestorLabel N ω q j n)
          (ancestorLabel N ω leftBoundaryProbe j n) =
        extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j n)
          (ancestorLabel N ω leftBoundaryProbe j n) \
            rebuildCutClade (extractOneSplitSkeleton N h) := by
  classical
  dsimp only
  have hn : n ≤ N + 1 := hnl.trans w.attach_bound.le
  obtain ⟨a, ha⟩ := w.detached_between n hcn hnl
  have hright := extractionRun_detached_right N h w.cutStep w.cutIndex w.cutPosition
    w.cut_index w.cut_event w.other_event q hq w.cutSample w.cut_sample n hn hcn a ha
  have hleft (j : Fin N) : ancestorLabel N (extractionPrefixExtension N h)
      leftBoundaryProbe j n ≠ a := by
    rw [← extractionRun_argLabels N h n hn j]
    exact ((extractionRun_inventory N h hs n hn).2.1.2.2 a ha).2 j
  obtain ⟨_, _, _, hc⟩ := w.cut_branch hs
  rw [w.cut_field] at hc
  simp only at hc
  have hform (b : ℕ) := ancestorClade_single_split_right N (extractionPrefixExtension N h)
    w.cutStep.val w.cutIndex w.cutPosition w.cut_pos w.cut_index w.cut_event
    (fun l hl => w.other_event l (by omega)) (fun l hl => w.other_event l (by omega))
    q hq w.cutSample w.cut_sample n hcn b
  simp only at hform
  have hempty : extractionClade (fun j => ancestorLabel N (extractionPrefixExtension N h)
      leftBoundaryProbe j n) a = ∅ := by
    ext j
    simp [extractionClade, hleft j]
  refine ⟨a, ?_, ?_⟩
  · rw [hform, hright, hempty, ite_eq_left rfl, Finset.empty_sdiff, Finset.empty_union, ← hc]
  · intro j
    rw [hform, hright, ite_eq_right (Ne.symm (hleft j)), Finset.union_empty, ← hc]

theorem OneSplitARGWitness.right_after {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) (hs : OneSplitPrefixSupported N h)
    (q : GenomicProbe) (hq : w.cutPosition ≤ (q.val : ℝ)) (n : ℕ)
    (hn : w.attachStep + 1 ≤ n) (a : ℕ) :
    extractionClade (fun j => ancestorLabel N (extractionPrefixExtension N h) q j n) a =
      regraftClade (rebuildCutClade (extractOneSplitSkeleton N h))
        (extractOneSplitSkeleton N h).2.2.2.2.2
        (extractionClade (fun j => ancestorLabel N (extractionPrefixExtension N h)
          leftBoundaryProbe j n) a) := by
  obtain ⟨_, _, _, hc⟩ := w.cut_branch hs
  rw [w.cut_field] at hc
  rw [hc, w.attach_field]
  exact ancestorClade_single_split_after_attachment N (extractionPrefixExtension N h)
    w.cutStep.val w.cutIndex w.cutPosition w.cut_pos w.cut_index w.cut_event
    (fun l hl => w.other_event l (by omega)) (fun l hl => w.other_event l (by omega))
    q hq w.cutSample w.targetSample w.cut_sample w.attachStep w.cut_before_attach
    w.pairIndex w.attach_event ⟨w.pair_order, w.pair_bound⟩ (w.pair_samples q hq) n hn a

end Rhone.Coalescent.SmcPrime
