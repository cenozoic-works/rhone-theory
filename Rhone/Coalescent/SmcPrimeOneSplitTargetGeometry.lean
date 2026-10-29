/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitARGWitness
public import Rhone.Coalescent.SmcPrimeOneSplitEpochGeometry

/-! # Target clades of the attachment in the extraction -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem OneSplitARGWitness.attach_hit {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) :
    ∃ a, (extractionRun N h w.attachStep).detached = some a ∧
      (a = liveLabelAt (extractionPrefixExtension N h w.attachStep).1 w.pairIndex.1 ∨
        a = liveLabelAt (extractionPrefixExtension N h w.attachStep).1 w.pairIndex.2) := by
  classical
  obtain ⟨a, ha, hanext⟩ := w.detached_present
  by_contra hmiss
  have he := w.attach_event
  rw [extractionPrefixExtension_prefix N h (w.attachStep + 1) w.attach_bound] at he
  rw [extractionPrefixExtension_prefix N h w.attachStep w.attach_bound.le] at hmiss
  rw [extractionRun_succ N h w.attachStep w.attach_bound] at hanext
  simp only [extractionStep, he, ite_eq_right hmiss] at hanext
  rw [ha] at hanext
  cases hanext

theorem OneSplitARGWitness.attachment_old_labels {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) :
    (extractionRun N h (w.attachStep + 1)).oldLabels =
      (extractionRun N h w.attachStep).oldLabels := by
  have he := w.attach_event
  have hhit := w.attach_hit
  rw [extractionPrefixExtension_prefix N h (w.attachStep + 1) w.attach_bound] at he
  rw [extractionPrefixExtension_prefix N h w.attachStep w.attach_bound.le] at hhit
  rw [extractionRun_succ N h w.attachStep w.attach_bound]
  simp only [extractionStep, he, ite_eq_left hhit]

theorem OneSplitARGWitness.target_fibre_after {N : ℕ} {h : ARGPrefix (N + 1)}
    (w : OneSplitARGWitness N h) (hs : OneSplitPrefixSupported N h) :
    extractionClade
      (fun j => ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j w.attachStep)
      (ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe w.targetSample
        w.attachStep) =
    extractionClade (extractionRun N h (w.attachStep + 1)).argLabels
      ((extractionRun N h (w.attachStep + 1)).argLabels w.targetSample) := by
  have hlabels : (fun j => ancestorLabel N (extractionPrefixExtension N h)
      leftBoundaryProbe j w.attachStep) = (extractionRun N h w.attachStep).argLabels :=
    funext (fun j => (extractionRun_argLabels N h w.attachStep w.attach_bound.le j).symm)
  have hpre := (extractionRun_inventory N h hs w.attachStep w.attach_bound.le).2.2.2.2
  have hpost := (extractionRun_inventory N h hs (w.attachStep + 1) w.attach_bound).2.2.2.2
  change extractionClade _ ((fun j => ancestorLabel N (extractionPrefixExtension N h)
    leftBoundaryProbe j w.attachStep) w.targetSample) = _
  rw [hlabels]
  ext j
  simp only [extractionClade, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hpre, hpost, w.attachment_old_labels]

theorem extractOneSplitSkeleton_target_timeClades (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    (extractOneSplitSkeleton N h).2.2.2.2.2 ∈
      timeClades (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
        (extractOneSplitSkeleton N h).2.2.2.2.1 := by
  classical
  obtain ⟨w⟩ := oneSplitARGWitness_exists N h hs
  rw [w.attach_field]
  simp only
  rw [w.target_fibre_after hs]
  rw [extractionPrefixExtension_prefix N h (w.attachStep + 1) w.attach_bound]
  by_cases hl : w.attachStep + 1 < N + 1
  · rw [extraction_timeClades_epoch N h hs (w.attachStep + 1) hl _ le_rfl
      (hs.clock_lt ⟨w.attachStep + 1, hl⟩)]
    exact Finset.mem_image.mpr ⟨w.targetSample, Finset.mem_univ _, rfl⟩
  · have hl' : w.attachStep + 1 = N + 1 := by have := w.attach_bound; omega
    have he : (⟨w.attachStep + 1, Finset.mem_Iic.mpr w.attach_bound⟩ : Finset.Iic (N + 1)) =
        ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hl'
    rw [he, hl', extraction_timeClades_terminal N h hs _ le_rfl]
    exact Finset.mem_image.mpr ⟨w.targetSample, Finset.mem_univ _, rfl⟩

end Rhone.Coalescent.SmcPrime
