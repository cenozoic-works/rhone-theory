/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeOneSplitEventTrace
public import Rhone.Coalescent.SmcPrimeOneSplitCutFields
public import Rhone.Coalescent.SmcPrimeOneSplitAttachmentFields
public import Rhone.Coalescent.SmcPrimeOneSplitNextOldRecord
public import Rhone.Coalescent.SmcPrimeOneSplitFutureClock
/-!
# Event time of a classified extraction event

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport
/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem extractionRebuildEvent_time (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (k : Fin (N + 1)) :
    rebuildEventTime (extractOneSplitSkeleton N h)
      (extractionRebuildEvent N (extractionRun N h k.val)
        (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)
        (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)) =
      (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).1.1 := by
  classical
  let z := extractionRun N h k.val
  let pre := h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩
  let next := h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩
  change rebuildEventTime (extractOneSplitSkeleton N h)
    (extractionRebuildEvent N z pre next) = next.1.1
  obtain ⟨c, hsplit, hcoal⟩ := hs.2.2.2.2.1
  by_cases hk : k = c
  · have hspl : next.2.2 ∈ splitSet := by simpa only [next, hk] using hsplit
    obtain ⟨i, x, _, _, hev, _, _⟩ := (hs.2.2.1 k).split_case (hs.2.1 _) hspl
    change next.2.2 = .inr (.inr (i.val, x)) at hev
    have hev' : (extractionPrefixExtension N h (c.val + 1)).2.2 =
        .inr (.inr (i.val, x)) := by
      rw [extractionPrefixExtension_prefix N h (c.val + 1) c.isLt]
      simpa only [next, hk] using hev
    have hfields := extractOneSplitSkeleton_cut_coordinates N h c i.val x hev'
      (extractionPrefixExtension_no_other_split N h c hcoal)
    simp only [extractionRebuildEvent, hev, rebuildEventTime]
    rw [hfields.1, extractionPrefixExtension_prefix N h (c.val + 1) c.isLt]
    subst k
    rfl
  · obtain ⟨i, j, _, hev, _, _⟩ := (hs.2.2.1 k).coal_case (hcoal k hk)
    change next.2.2 = .inr (.inl (i.val, j.val)) at hev
    by_cases hhit : ∃ d, z.detached = some d ∧
        (d = liveLabelAt pre.1 i.val ∨ d = liveLabelAt pre.1 j.val)
    · have hhitcopy := hhit
      obtain ⟨d, hd, _⟩ := hhitcopy
      have hcn : c.val < k.val := by
        by_contra hnot
        have hnone := extractionRun_detached_before_split N h c hcoal k.val (by omega)
        change z.detached = none at hnone
        rw [hd] at hnone
        cases hnone
      have hother : ∀ m, k.val < m → CoalOrStop (extractionPrefixExtension N h (m + 1)).2.2 :=
        fun m hm => extractionPrefixExtension_no_other_split N h c hcoal m (by omega)
      have hev' : (extractionPrefixExtension N h (k.val + 1)).2.2 =
          .inr (.inl (i.val, j.val)) := by
        rw [extractionPrefixExtension_prefix N h (k.val + 1) k.isLt]
        exact hev
      have hhit' : ∃ d, (extractionRun N h k.val).detached = some d ∧
          (d = liveLabelAt (extractionPrefixExtension N h k.val).1 i.val ∨
           d = liveLabelAt (extractionPrefixExtension N h k.val).1 j.val) := by
        rw [extractionPrefixExtension_prefix N h k.val k.isLt.le]
        exact hhit
      have hfields := extractOneSplitSkeleton_attachment_fields N h k.val k.isLt
        (i.val, j.val) hev' hhit' hother
      simp only [extractionRebuildEvent, hev, ite_eq_left hhit, rebuildEventTime]
      have ht := congrArg Prod.fst hfields
      simpa only [extractionPrefixExtension_prefix N h (k.val + 1) k.isLt] using ht
    · have hm : (extractionRun N h (k.val + 1)).mergers = z.mergers + 1 := by
        rw [extractionRun_succ N h k.val k.isLt]
        change (extractionStep z pre next).mergers = z.mergers + 1
        simp only [extractionStep, hev, ite_eq_right hhit]
      have hb : z.mergers < N - 1 := by
        have hh := (extractionRun_history_prefix N h hs (k.val + 1) k.isLt).bound
        rw [hm] at hh
        omega
      simp only [extractionRebuildEvent, hev, ite_eq_right hhit, dite_eq_left hb,
        rebuildEventTime]
      rw [extractionRun_next_old_record N h hs k.val k.isLt hm,
        extractionRun_succ N h k.val k.isLt]
      change (extractionStep z pre next).old.1.1 = next.1.1
      simp only [extractionStep, hev, ite_eq_right hhit, rebuildCoal, atTime]
end Rhone.Coalescent.SmcPrime
