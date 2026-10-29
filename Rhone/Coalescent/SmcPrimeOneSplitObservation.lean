/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightTimeClades
public import Rhone.Coalescent.SmcPrimePrefixMRCAClades
public import Rhone.Coalescent.SmcPrimeOneSplitExposureSupport
public import Rhone.Coalescent.SmcPrimeOneSplitCarrierSupport
public import Rhone.Coalescent.SmcPrimeOneSectorLaw

/-! # Pairwise MRCA observation of the one-split extraction at rational sites -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem oneSplitPrefix_left_labels (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (q : GenomicProbe)
    (hq : (q.val : ℝ) < (extractOneSplitSkeleton N h).2.2.2.1) (j : Fin N) (n : ℕ) :
    ancestorLabel N (extractionPrefixExtension N h) q j n =
      ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j n := by
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  have hx := (extractOneSplitSkeleton_cut_coordinates N h w.cutStep w.cutIndex
    w.cutPosition w.cut_event w.other_event).2
  have hqx : (q.val : ℝ) < w.cutPosition := by rwa [hx] at hq
  have hstep (k a : ℕ) : ancestorStep (extractionPrefixExtension N h k).1
        (extractionPrefixExtension N h (k + 1)).2.2 q a =
      ancestorStep (extractionPrefixExtension N h k).1
        (extractionPrefixExtension N h (k + 1)).2.2 leftBoundaryProbe a := by
    by_cases hk : k = w.cutStep.val
    · subst k
      rw [w.cut_event]
      simp [ancestorStep, w.cut_index, hqx, leftBoundaryProbe, w.cut_pos]
    · exact ancestorStep_coalOrStop _ _ (w.other_event k hk) q leftBoundaryProbe a
  induction n with
  | zero => rfl
  | succ n ih => simp only [ancestorLabel, hstep, ih]

theorem oneSplitPrefix_terminal_labels (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (q : GenomicProbe) (i j : Fin N) :
    ancestorLabel N (extractionPrefixExtension N h) q i (N + 1) =
      ancestorLabel N (extractionPrefixExtension N h) q j (N + 1) := by
  obtain ⟨a, ha, _⟩ := oneSplitPrefix_ancestorCarried N h hs q i (N + 1) le_rfl
  obtain ⟨b, hb, _⟩ := oneSplitPrefix_ancestorCarried N h hs q j (N + 1) le_rfl
  have hc : (extractionPrefixExtension N h (N + 1)).1.2.2.1 = 1 := by
    rw [extractionPrefixExtension_prefix N h (N + 1) le_rfl]
    exact hs.2.2.2.2.2
  have he : a = b := by
    apply Fin.ext
    have ha' := a.isLt
    have hb' := b.isLt
    omega
  exact ha.symm.trans (he ▸ hb)

theorem extractOneSplitSkeleton_genealogy (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    oneSkeletonGenealogy N (extractOneSplitSkeleton N h) =
      prefixGenealogyObservation N (N + 1) (extractionPrefixExtension N h) := by
  classical
  funext q i j
  let η := extractOneSplitSkeleton N h
  let ω := extractionPrefixExtension N h
  let T := if (q.val : ℝ) < η.2.2.2.1 then metricTreeFromHistory N η.1
    else oneSplitPostTree η
  have hk := extractOneSplitSkeleton_history_supported N h hs
  have hn := metric_tree_from_history_normalized N η.1
  have hnn := metric_tree_from_history_nonnegative N η.1 (fun k => (hk.1 k).1.1)
  have hchron := metric_tree_from_history_chronology N η.1 hs.sample_pos hk
  have hpost := extractOneSplitSkeleton_post_geometry N h hs
  have hroot := extractOneSplitSkeleton_root_bounds N h hs
  have hgeom : TreeNormalized T ∧ TreeNonnegative T ∧ TreeChronology T ∧
      rootHeight T ≤ (ω (N + 1)).1.1 := by
    dsimp only [ω]
    rw [extractionPrefixExtension_prefix N h (N + 1) le_rfl]
    by_cases hq : (q.val : ℝ) < η.2.2.2.1
    · simpa only [T, hq, ite_true] using And.intro hn ⟨hnn, hchron, hroot.1⟩
    · simpa only [T, hq, ite_false] using
        And.intro hpost.1 ⟨hpost.2.1, hpost.2.2.1, hroot.2⟩
  have hzero : (ω 0).1.1 = 0 := by
    simp only [ω, extractionPrefixExtension_prefix N h 0 (by omega), hs.1]
    rfl
  have htimes (k : ℕ) (hk : k ≤ N + 1) : 0 ≤ (ω k).1.1 := by
    simp only [ω, extractionPrefixExtension_prefix N h k hk]
    exact hs.clock_nonneg _
  have hstrict (k : ℕ) (hk : k < N + 1) : (ω k).1.1 < (ω (k + 1)).1.1 := by
    simp only [ω, extractionPrefixExtension_prefix N h k hk.le,
      extractionPrefixExtension_prefix N h (k + 1) hk]
    exact hs.clock_lt ⟨k, hk⟩
  have hclades (k : ℕ) (hk : k < N + 1) (y : ℝ)
      (hlo : (ω k).1.1 ≤ y) (hhi : y < (ω (k + 1)).1.1) :
      timeClades T y = Finset.univ.image (fun j =>
        extractionClade (fun a => ancestorLabel N ω q a k) (ancestorLabel N ω q j k)) := by
    by_cases hq : (q.val : ℝ) < η.2.2.2.1
    · simp only [T, hq, ite_true]
      rw [extraction_timeClades_epoch_labels N h hs k hk y hlo hhi]
      have hf : (fun a => ancestorLabel N ω q a k) =
          fun a => ancestorLabel N ω leftBoundaryProbe a k :=
        funext (fun a => oneSplitPrefix_left_labels N h hs q hq a k)
      rw [hf]
      simp only [ω, oneSplitPrefix_left_labels N h hs q hq]
    · simp only [T, hq, ite_false]
      exact extractOneSplitSkeleton_right_timeClades N h hs q (le_of_not_gt hq)
        k hk y hlo hhi
  have he := treePairMRCA_eq_prefix_of_timeClades N (N + 1) ω q T hgeom.1 hgeom.2.1
    hgeom.2.2.1 hzero htimes hstrict hgeom.2.2.2
    (oneSplitPrefix_terminal_labels N h hs q) hclades i j
  change (if (q.val : ℝ) < η.2.2.2.1 then treePairMRCA (metricTreeFromHistory N η.1) i j
    else treePairMRCA (oneSplitPostTree η) i j) = _
  simpa only [T, apply_ite (fun U => treePairMRCA U i j)] using he

end Rhone.Coalescent.SmcPrime
