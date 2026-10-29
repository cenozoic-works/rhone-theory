/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightCut

/-! # The attachment record persists in the final extraction -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem extractionStep_attachment_stable {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (hd : z.detached = none) (he : CoalOrStop next.2.2) :
    (extractionStep z pre next).detached = none ∧
      (extractionStep z pre next).attachment = z.attachment := by
  classical
  rcases he with he | ⟨ij, he⟩ <;> simp [extractionStep, he, hd]

theorem extractionRun_attachment_stable (N : ℕ) (h : ARGPrefix (N + 1))
    (l : ℕ) (hd : (extractionRun N h l).detached = none)
    (hother : ∀ m, l ≤ m → CoalOrStop (extractionPrefixExtension N h (m + 1)).2.2)
    (n : ℕ) (hn : n ≤ N + 1) (hln : l ≤ n) :
    (extractionRun N h n).detached = none ∧
      (extractionRun N h n).attachment = (extractionRun N h l).attachment := by
  induction n, hln using Nat.le_induction with
  | base => exact ⟨hd, rfl⟩
  | succ n hln ih =>
    obtain ⟨hnone, hatt⟩ := ih (by omega)
    rw [extractionRun_succ N h n (by omega)]
    have he : CoalOrStop (h ⟨n + 1, Finset.mem_Iic.mpr hn⟩).2.2 := by
      simpa only [extractionPrefixExtension_prefix N h (n + 1) hn] using hother n hln
    obtain ⟨hd', ha'⟩ := extractionStep_attachment_stable (extractionRun N h n)
      (h ⟨n, Finset.mem_Iic.mpr (by omega)⟩) (h ⟨n + 1, Finset.mem_Iic.mpr hn⟩) hnone he
    exact ⟨hd', ha'.trans hatt⟩

theorem extractionStep_attachment_field {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (ij : ℕ × ℕ)
    (hev : next.2.2 = .inr (.inl ij))
    (hhit : ∃ a, z.detached = some a ∧
      (a = liveLabelAt pre.1 ij.1 ∨ a = liveLabelAt pre.1 ij.2)) :
    (extractionStep z pre next).detached = none ∧
      (extractionStep z pre next).attachment =
        (next.1.1, extractionClade z.argLabels
          (if z.detached = some (liveLabelAt pre.1 ij.1)
            then liveLabelAt pre.1 ij.2 else liveLabelAt pre.1 ij.1)) := by
  classical
  simp only [extractionStep, hev, hhit, ↓reduceIte]
  exact ⟨True.intro, True.intro⟩

theorem extractOneSplitSkeleton_attachment_fields (N : ℕ) (h : ARGPrefix (N + 1))
    (l : ℕ) (hl : l < N + 1) (ij : ℕ × ℕ)
    (hev : (extractionPrefixExtension N h (l + 1)).2.2 = .inr (.inl ij))
    (hhit : ∃ a, (extractionRun N h l).detached = some a ∧
      (a = liveLabelAt (extractionPrefixExtension N h l).1 ij.1 ∨
        a = liveLabelAt (extractionPrefixExtension N h l).1 ij.2))
    (hother : ∀ m, l < m → CoalOrStop (extractionPrefixExtension N h (m + 1)).2.2) :
    (extractOneSplitSkeleton N h).2.2.2.2 =
      ((extractionPrefixExtension N h (l + 1)).1.1,
        extractionClade (fun j => ancestorLabel N (extractionPrefixExtension N h)
          leftBoundaryProbe j l)
        (if (extractionRun N h l).detached =
              some (liveLabelAt (extractionPrefixExtension N h l).1 ij.1)
          then liveLabelAt (extractionPrefixExtension N h l).1 ij.2
          else liveLabelAt (extractionPrefixExtension N h l).1 ij.1)) := by
  classical
  have hev' := hev
  rw [extractionPrefixExtension_prefix N h (l + 1) hl] at hev'
  have hhit' := hhit
  rw [extractionPrefixExtension_prefix N h l hl.le] at hhit'
  have hstep := extractionStep_attachment_field (extractionRun N h l)
    (h ⟨l, Finset.mem_Iic.mpr hl.le⟩) (h ⟨l + 1, Finset.mem_Iic.mpr hl⟩) ij hev' hhit'
  rw [← extractionRun_succ N h l hl] at hstep
  have hstable := extractionRun_attachment_stable N h (l + 1) hstep.1
    (fun m hm => hother m (by omega)) (N + 1) le_rfl hl
  change (extractionRun N h (N + 1)).attachment = _
  rw [hstable.2, hstep.2]
  have hlab : (extractionRun N h l).argLabels =
      fun j => ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j l :=
    funext (extractionRun_argLabels N h l hl.le)
  simp only [hlab, extractionPrefixExtension_prefix N h l hl.le,
    extractionPrefixExtension_prefix N h (l + 1) hl]

end Rhone.Coalescent.SmcPrime
