/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitSkeletonAttachment
public import Rhone.Coalescent.SmcPrimeOneSplitCutFields

/-! # Event witnesses with the exact stored skeleton fields -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

structure OneSplitARGWitness (N : ℕ) (h : ARGPrefix (N + 1)) where
  cutStep : Fin (N + 1)
  cutIndex : ℕ
  cutPosition : ℝ
  cutSample : Fin N
  attachStep : ℕ
  pairIndex : ℕ × ℕ
  targetSample : Fin N
  cut_pos : 0 < cutPosition
  cut_lt_one : cutPosition < 1
  cut_index : cutIndex < (extractionPrefixExtension N h cutStep.val).1.2.2.1
  cut_event : (extractionPrefixExtension N h (cutStep.val + 1)).2.2 =
    .inr (.inr (cutIndex, cutPosition))
  other_event : ∀ l, l ≠ cutStep.val →
    CoalOrStop (extractionPrefixExtension N h (l + 1)).2.2
  cut_sample : ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe
    cutSample cutStep.val = liveLabelAt (extractionPrefixExtension N h cutStep.val).1 cutIndex
  cut_before_attach : cutStep.val < attachStep
  attach_bound : attachStep < N + 1
  attach_event : (extractionPrefixExtension N h (attachStep + 1)).2.2 = .inr (.inl pairIndex)
  pair_order : pairIndex.1 < pairIndex.2
  pair_bound : pairIndex.2 < (extractionPrefixExtension N h attachStep).1.2.2.1
  detached_present : ∃ a, (extractionRun N h attachStep).detached = some a ∧
    (extractionRun N h (attachStep + 1)).detached = none
  cut_field : (extractionRun N h (N + 1)).cut =
    (extractionClade
      (fun j => ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j cutStep.val)
      (liveLabelAt (extractionPrefixExtension N h cutStep.val).1 cutIndex),
      (extractionPrefixExtension N h (cutStep.val + 1)).1.1, cutPosition)
  attach_field : (extractOneSplitSkeleton N h).2.2.2.2 =
    ((extractionPrefixExtension N h (attachStep + 1)).1.1,
      extractionClade
        (fun j => ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j attachStep)
        (ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe targetSample attachStep))
  pair_samples : ∀ q : GenomicProbe, cutPosition ≤ (q.val : ℝ) →
    (ancestorLabel N (extractionPrefixExtension N h) q cutSample attachStep =
        liveLabelAt (extractionPrefixExtension N h attachStep).1 pairIndex.1 ∧
      ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe targetSample attachStep =
        liveLabelAt (extractionPrefixExtension N h attachStep).1 pairIndex.2) ∨
    (ancestorLabel N (extractionPrefixExtension N h) q cutSample attachStep =
        liveLabelAt (extractionPrefixExtension N h attachStep).1 pairIndex.2 ∧
      ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe targetSample attachStep =
        liveLabelAt (extractionPrefixExtension N h attachStep).1 pairIndex.1)

theorem oneSplitARGWitness_exists (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) : Nonempty (OneSplitARGWitness N h) := by
  obtain ⟨c, i, x, r, hx0, hx1, hi, hev, hother, hr⟩ := oneSplitPrefix_cut_data N h hs
  obtain ⟨l, hcl, hl, ij, d, hpair, hij, hj, hdet, hf, hp⟩ :=
    oneSplitPrefix_attachment_target N h hs c i x hx1 hi hev hother r hr
  exact ⟨⟨c, i, x, r, l, ij, d, hx0, hx1, hi, hev, hother, hr, hcl, hl, hpair, hij, hj,
    hdet, extractionRun_cut_after_split N h c i x hev hother (N + 1) le_rfl c.isLt, hf, hp⟩⟩

end Rhone.Coalescent.SmcPrime
