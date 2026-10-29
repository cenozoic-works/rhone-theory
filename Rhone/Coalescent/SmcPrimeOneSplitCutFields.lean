/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightCut

/-! # Cut fields of the terminal extraction -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem extractionStep_cut_of_coalOrStop {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) (he : CoalOrStop next.2.2) :
    (extractionStep z pre next).cut = z.cut := by
  classical
  rcases he with he | ⟨ij, he⟩
  · simp only [extractionStep, he]
  · simp only [extractionStep, he]
    split <;> rfl

theorem extractionRun_cut_after_split (N : ℕ) (h : ARGPrefix (N + 1))
    (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hev : (extractionPrefixExtension N h (c.val + 1)).2.2 = .inr (.inr (i, x)))
    (hother : ∀ l, l ≠ c.val → CoalOrStop (extractionPrefixExtension N h (l + 1)).2.2)
    (n : ℕ) (hn : n ≤ N + 1) (hcn : c.val + 1 ≤ n) :
    (extractionRun N h n).cut =
      (extractionClade
        (fun j => ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j c.val)
        (liveLabelAt (extractionPrefixExtension N h c.val).1 i),
      (extractionPrefixExtension N h (c.val + 1)).1.1, x) := by
  classical
  induction n, hcn using Nat.le_induction with
  | base =>
    have hev' : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 = .inr (.inr (i, x)) := by
      simpa only [extractionPrefixExtension_prefix N h (c.val + 1) c.isLt] using hev
    have hlab : (extractionRun N h c.val).argLabels =
        fun j => ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe j c.val :=
      funext (extractionRun_argLabels N h c.val c.isLt.le)
    rw [extractionRun_succ N h c.val c.isLt]
    simp only [extractionStep, hev', hlab,
      extractionPrefixExtension_prefix N h c.val c.isLt.le,
      extractionPrefixExtension_prefix N h (c.val + 1) c.isLt]
  | succ n hcn ih =>
    rw [extractionRun_succ N h n (by omega), extractionStep_cut_of_coalOrStop]
    · exact ih (by omega)
    · simpa only [extractionPrefixExtension_prefix N h (n + 1) hn] using hother n (by omega)

theorem extractOneSplitSkeleton_cut_coordinates (N : ℕ) (h : ARGPrefix (N + 1))
    (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hev : (extractionPrefixExtension N h (c.val + 1)).2.2 = .inr (.inr (i, x)))
    (hother : ∀ l, l ≠ c.val → CoalOrStop (extractionPrefixExtension N h (l + 1)).2.2) :
    (extractOneSplitSkeleton N h).2.2.1 = (extractionPrefixExtension N h (c.val + 1)).1.1 ∧
      (extractOneSplitSkeleton N h).2.2.2.1 = x := by
  have he := extractionRun_cut_after_split N h c i x hev hother (N + 1) le_rfl c.isLt
  change (extractionRun N h (N + 1)).cut.2.1 = _ ∧
    (extractionRun N h (N + 1)).cut.2.2 = x
  rw [he]
  exact ⟨rfl, rfl⟩

end Rhone.Coalescent.SmcPrime
