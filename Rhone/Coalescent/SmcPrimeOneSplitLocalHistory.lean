/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitHistoryPrefix
public import Rhone.Coalescent.SmcPrimeOneSplitClockInventory

/-! # Pair, split, and attachment steps append supported Kingman records to the extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem extractionStep_old_pair_history {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (h : ExtractionInventory z pre.1) (hs : Valid pre.1)
    (hh : ExtractedHistoryPrefix N z) (hc : z.old.1.1 ≤ pre.1.1)
    (ht : pre.1.1 < next.1.1) (i j : Fin pre.1.2.2.1) (hij : i.val < j.val)
    (hev : next.2.2 = .inr (.inl (i.val, j.val)))
    (hi : z.detached ≠ some (pre.1.2.2.2 i).1)
    (hj : z.detached ≠ some (pre.1.2.2.2 j).1) :
    ExtractedHistoryPrefix N (extractionStep z pre next) := by
  classical
  obtain ⟨p, q, hpq, hold, _⟩ :=
    extractionStep_old_pair z pre next h hs i j hij hev hi hj
  have hcurcount := (hh.records ⟨z.mergers, hh.bound⟩ le_rfl).2
  rw [hh.current] at hcurcount
  change z.old.1.2.2.1 = N - z.mergers at hcurcount
  have hm : 2 ≤ z.old.1.2.2.1 := by have := q.isLt; omega
  have hb : z.mergers + 1 < N := by omega
  have hy : Valid (extractionStep z pre next).old.1 := by
    rw [hold]
    exact SmcSupport.atTime_valid _ (SmcSupport.coalSuccessor_valid _ h.1 p q) _
      ((hs.1.trans_lt ht).le)
  have hycount : (extractionStep z pre next).old.1.2.2.1 + 1 = z.old.1.2.2.1 := by
    rw [hold]
    exact SmcSupport.coalSuccessor_count _ p q hpq
  have hytrans : KingmanTransition (z.old, (extractionStep z pre next).old) := by
    rw [hold]
    simp only [KingmanTransition, ite_eq_left hm]
    refine ⟨(p.val, q.val), hpq, q.isLt, rfl, ?_, hc.trans_lt ht⟩
    simp only [coalSuccessorNat, dite_eq_left p.isLt, dite_eq_left q.isLt]
    rfl
  have hiuid : liveLabelAt pre.1 i.val = (pre.1.2.2.2 i).1 := by
    simp only [liveLabelAt, dite_eq_left i.isLt]
  have hjuid : liveLabelAt pre.1 j.val = (pre.1.2.2.2 j).1 := by
    simp only [liveLabelAt, dite_eq_left j.isLt]
  have hnattach : ¬ ∃ d, z.detached = some d ∧
      (d = (pre.1.2.2.2 i).1 ∨ d = (pre.1.2.2.2 j).1) := by
    rintro ⟨d, hd, hdi | hdj⟩
    · exact hi (hd.trans (congrArg some hdi))
    · exact hj (hd.trans (congrArg some hdj))
  have hfields : (extractionStep z pre next).oldHistory =
      Function.update z.oldHistory ⟨z.mergers + 1, hb⟩ (extractionStep z pre next).old ∧
      (extractionStep z pre next).mergers = z.mergers + 1 := by
    simp only [extractionStep, hev, hiuid, hjuid, ite_eq_right hnattach, dite_eq_left hb]
    exact ⟨True.intro, True.intro⟩
  exact (hh.advance _ hb hy hycount hytrans).congr_fields rfl hfields.1 hfields.2

theorem extractionStep_split_history {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (hh : ExtractedHistoryPrefix N z) (ix : ℕ × ℝ)
    (hev : next.2.2 = .inr (.inr ix)) :
    ExtractedHistoryPrefix N (extractionStep z pre next) := by
  apply hh.congr_fields
  · simp only [extractionStep, hev]
  · simp only [extractionStep, hev]
  · simp only [extractionStep, hev]

theorem extractionStep_attachment_history {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (hh : ExtractedHistoryPrefix N z) (ij : ℕ × ℕ)
    (hev : next.2.2 = .inr (.inl ij))
    (hd : ∃ d, z.detached = some d ∧
      (d = liveLabelAt pre.1 ij.1 ∨ d = liveLabelAt pre.1 ij.2)) :
    ExtractedHistoryPrefix N (extractionStep z pre next) := by
  apply hh.congr_fields
  · simp only [extractionStep, hev, ite_eq_left hd]
  · simp only [extractionStep, hev, ite_eq_left hd]
  · simp only [extractionStep, hev, ite_eq_left hd]

end Rhone.Coalescent.SmcPrime
