/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitTargetGeometry
public import Rhone.Coalescent.SmcPrimeOneSplitCutBranch
public import Rhone.Coalescent.SmcPrimeProposalSkeleton
public import Rhone.Coalescent.SmcPrimeRegraftActiveUnique
public import Rhone.Coalescent.SmcPrimeKingmanNonnegative

/-! # Tree geometry of the extracted cut and post-regraft trees -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem oneSplitPostTree_regraft {N : ℕ} (η : OneSplitSkeleton N) :
    oneSplitPostTree η = regraft (metricTreeFromHistory N η.1) (rebuildCutClade η)
      η.2.2.2.2.2 η.2.2.1 η.2.2.2.2.1 := by
  classical
  unfold oneSplitPostTree forgetCutIndex rebuildCutClade
  dsimp only
  split_ifs <;> rfl

theorem OneSplitARGWitness.cut_branch {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) (hs : OneSplitPrefixSupported N h) :
    ∃ b : Fin (metricTreeFromHistory N (extractOneSplitSkeleton N h).1).1,
      b ∈ activeBranches (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
        (extractOneSplitSkeleton N h).2.2.1 ∧
      ((metricTreeFromHistory N (extractOneSplitSkeleton N h).1).2 b).1 =
        rebuildCutClade (extractOneSplitSkeleton N h) ∧
      rebuildCutClade (extractOneSplitSkeleton N h) =
        (extractionRun N h (N + 1)).cut.1 := by
  classical
  have hi := w.cut_index
  rw [extractionPrefixExtension_prefix N h w.cutStep.val w.cutStep.isLt.le] at hi
  have hev := w.cut_event
  rw [extractionPrefixExtension_prefix N h (w.cutStep.val + 1) w.cutStep.isLt] at hev
  obtain ⟨b, hb, hidx, hclade⟩ := extractOneSplitSkeleton_cut_branch N h hs
    w.cutStep ⟨w.cutIndex, hi⟩ w.cutPosition hev
  have hvalid : (extractOneSplitSkeleton N h).2.1 <
      (metricTreeFromHistory N (extractOneSplitSkeleton N h).1).1 := by
    rw [hidx]
    exact b.isLt
  have he : (⟨(extractOneSplitSkeleton N h).2.1, hvalid⟩ :
      Fin (metricTreeFromHistory N (extractOneSplitSkeleton N h).1).1) = b := Fin.ext hidx
  refine ⟨b, hb, ?_, ?_⟩
  · simp only [rebuildCutClade, dite_eq_left hvalid, he]
  · rw [w.cut_field]
    simp only
    have hlabels : (fun j => ancestorLabel N (extractionPrefixExtension N h)
        leftBoundaryProbe j w.cutStep.val) = (extractionRun N h w.cutStep.val).argLabels :=
      funext (fun j => (extractionRun_argLabels N h w.cutStep.val w.cutStep.isLt.le j).symm)
    rw [hlabels, extractionPrefixExtension_prefix N h w.cutStep.val w.cutStep.isLt.le]
    simpa only [liveLabelAt, dite_eq_left hi] using hclade

theorem extractOneSplitSkeleton_cut_geometry (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    let η := extractOneSplitSkeleton N h
    let T := metricTreeFromHistory N η.1
    0 ≤ η.2.2.1 ∧ η.2.2.1 ≤ η.2.2.2.2.1 ∧ η.2.2.1 ≤ rootHeight T ∧
      rebuildCutClade η ∈ timeClades T η.2.2.1 ∧
      rebuildCutClade η ≠ ∅ ∧ rebuildCutClade η ≠ Finset.univ := by
  classical
  dsimp only
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  obtain ⟨b, hb, hc, _⟩ := w.cut_branch hs
  have hp := (Finset.mem_filter.mp hb).2
  have hroot : (extractOneSplitSkeleton N h).2.2.1 <
      rootHeight (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) :=
    hp.2.2.trans_le (branch_hi_le_root _ b hp.1)
  have hcut := (extractOneSplitSkeleton_cut_coordinates N h w.cutStep w.cutIndex
    w.cutPosition w.cut_event w.other_event).1
  have ht : 0 ≤ (extractOneSplitSkeleton N h).2.2.1 := by
    rw [hcut, extractionPrefixExtension_prefix N h (w.cutStep.val + 1) w.cutStep.isLt]
    exact hs.clock_nonneg _
  have hta : (extractOneSplitSkeleton N h).2.2.1 ≤
      (extractOneSplitSkeleton N h).2.2.2.2.1 := by
    rw [hcut, w.attach_field]
    simp only
    rw [extractionPrefixExtension_prefix N h (w.cutStep.val + 1) w.cutStep.isLt,
      extractionPrefixExtension_prefix N h (w.attachStep + 1) w.attach_bound]
    exact hs.clock_mono _ _ (by have := w.cut_before_attach; omega) w.attach_bound
  refine ⟨ht, hta, hroot.le, ?_, ?_, ?_⟩
  · simp only [timeClades, not_le.mpr hroot, ↓reduceIte, Finset.mem_image]
    exact ⟨b, hb, hc⟩
  · intro he
    simp [branchLength, hc, he] at hp
  · intro he
    simp [branchLength, hc, he] at hp

theorem extractOneSplitSkeleton_post_geometry (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    TreeNormalized (oneSplitPostTree (extractOneSplitSkeleton N h)) ∧
      TreeNonnegative (oneSplitPostTree (extractOneSplitSkeleton N h)) ∧
      TreeChronology (oneSplitPostTree (extractOneSplitSkeleton N h)) ∧
      TreeActiveUnique (oneSplitPostTree (extractOneSplitSkeleton N h)) := by
  have hk := extractOneSplitSkeleton_history_supported N h hs
  have hn := metric_tree_from_history_normalized N (extractOneSplitSkeleton N h).1
  have hc := metric_tree_from_history_chronology N _ hs.sample_pos hk
  have hu := metric_tree_from_history_active_unique N _ hs.sample_pos hk
  have hnn := metric_tree_from_history_nonnegative N _ (fun k => (hk.1 k).1.1)
  obtain ⟨ht, hta, _, hcut, hs0, hs1⟩ := extractOneSplitSkeleton_cut_geometry N h hs
  have htarget := extractOneSplitSkeleton_target_timeClades N h hs
  rw [oneSplitPostTree_regraft]
  exact ⟨regraft_normalized _ _ _ _ _, regraft_nonnegative _ _ _ _ _ hnn ht,
    regraft_chronology _ _ _ _ _ hn hc ht hta hcut hs0 hs1 htarget,
    regraft_active_unique _ _ _ _ _ hn hc hu ht hta hcut hs0 hs1 htarget⟩

end Rhone.Coalescent.SmcPrime
