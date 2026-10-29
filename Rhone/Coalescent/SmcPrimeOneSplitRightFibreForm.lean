/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightEpochGeometry

/-! # Right sample fibres have the regraft clade form -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem extractOneSplitSkeleton_right_fibre_form (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (q : GenomicProbe)
    (hq : (extractOneSplitSkeleton N h).2.2.2.1 ≤ (q.val : ℝ))
    (n : ℕ) (hn : n < N + 1) (y : ℝ)
    (hlo : (extractionPrefixExtension N h n).1.1 ≤ y)
    (hhi : y < (extractionPrefixExtension N h (n + 1)).1.1) (j : Fin N) :
    RegraftCladeAt (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
      (rebuildCutClade (extractOneSplitSkeleton N h)) (extractOneSplitSkeleton N h).2.2.2.2.2
      (extractOneSplitSkeleton N h).2.2.1 (extractOneSplitSkeleton N h).2.2.2.2.1 y
      (extractionClade (fun a => ancestorLabel N (extractionPrefixExtension N h) q a n)
        (ancestorLabel N (extractionPrefixExtension N h) q j n)) := by
  classical
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  let f := fun a => ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe a n
  let g := fun a => ancestorLabel N (extractionPrefixExtension N h) q a n
  let S := rebuildCutClade (extractOneSplitSkeleton N h)
  have hj : j ∈ extractionClade g (g j) := by simp [extractionClade]
  have hcoords := extractOneSplitSkeleton_cut_coordinates N h w.cutStep w.cutIndex
    w.cutPosition w.cut_event w.other_event
  have hqx : w.cutPosition ≤ (q.val : ℝ) := by rwa [hcoords.2] at hq
  have hcutphase := hs.epoch_before_event n hn y hlo hhi w.cutStep.val w.cutStep.isLt
  have hattphase := hs.epoch_before_event n hn y hlo hhi w.attachStep w.attach_bound
  rw [← hcoords.1] at hcutphase
  have hattclock : (extractOneSplitSkeleton N h).2.2.2.2.1 =
      (extractionPrefixExtension N h (w.attachStep + 1)).1.1 := congrArg Prod.fst w.attach_field
  rw [← hattclock] at hattphase
  have hold (a : Fin N) : extractionClade f (f a) ∈
      timeClades (metricTreeFromHistory N (extractOneSplitSkeleton N h).1) y := by
    rw [extraction_timeClades_epoch_labels N h hs n hn y hlo hhi]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  by_cases hyt : y < (extractOneSplitSkeleton N h).2.2.1
  · apply Or.inl
    refine ⟨hyt, ?_⟩
    have he : g = f := funext (fun a => w.right_before q a n (hcutphase.mp hyt))
    change extractionClade g (g j) ∈ _
    rw [he]
    exact hold j
  · have hty := le_of_not_gt hyt
    by_cases hya : y < (extractOneSplitSkeleton N h).2.2.2.2.1
    · apply Or.inr ∘ Or.inl
      refine ⟨hty, hya, ?_⟩
      have hcn : w.cutStep.val + 1 ≤ n := by
        have hh : ¬ n ≤ w.cutStep.val := fun he => hyt (hcutphase.mpr he)
        omega
      have hnl : n ≤ w.attachStep := hattphase.mp hya
      obtain ⟨a, ha, hleft⟩ := w.right_middle hs q hqx n hcn hnl
      change extractionClade g a = S at ha
      by_cases hjs : j ∈ S
      · have hja : g j = a := by
          simpa only [extractionClade, Finset.mem_filter, Finset.mem_univ, true_and]
            using (show j ∈ extractionClade g a from ha.symm ▸ hjs)
        exact Or.inl (by change extractionClade g (g j) = S; rw [hja, ha])
      · have hmem : j ∈ extractionClade f (f j) \ S := by
          exact Finset.mem_sdiff.mpr ⟨by simp [extractionClade], hjs⟩
        have hjf : g j = f j := by
          simpa only [extractionClade, Finset.mem_filter, Finset.mem_univ, true_and]
            using (show j ∈ extractionClade g (f j) from (hleft j).symm ▸ hmem)
        refine Or.inr ⟨extractionClade f (f j), hold j, ?_⟩
        change extractionClade g (g j) = _
        rw [hjf]
        exact hleft j
    · apply Or.inr ∘ Or.inr
      have hay := le_of_not_gt hya
      have hln : w.attachStep + 1 ≤ n := by
        have hh : ¬ n ≤ w.attachStep := fun he => hya (hattphase.mpr he)
        omega
      have he := w.right_after hs q hqx n hln (g j)
      change extractionClade g (g j) = regraftClade S
        (extractOneSplitSkeleton N h).2.2.2.2.2 (extractionClade f (g j)) at he
      have hne : extractionClade f (g j) ≠ ∅ := by
        intro hzero
        have hz : extractionClade g (g j) = ∅ := by
          rw [he, hzero]
          simp [regraftClade, aboveAttachment, finiteBranch]
        rw [hz] at hj
        exact Finset.notMem_empty _ hj
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hfa : f a = g j := (Finset.mem_filter.mp ha).2
      exact ⟨hay, extractionClade f (f a), hold a, by rw [hfa]; exact he⟩

end Rhone.Coalescent.SmcPrime
