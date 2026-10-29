/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightCut

/-! # The detached lineage in the extraction and its disappearance at attachment -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem extractionRun_detached_right (N : ℕ) (h : ARGPrefix (N + 1))
    (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hi : i < (extractionPrefixExtension N h c.val).1.2.2.1)
    (hev : (extractionPrefixExtension N h (c.val + 1)).2.2 = .inr (.inr (i, x)))
    (hother : ∀ l, l ≠ c.val → CoalOrStop (extractionPrefixExtension N h (l + 1)).2.2)
    (q : GenomicProbe) (hq : x ≤ (q.val : ℝ)) (r : Fin N)
    (hr : ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe r c.val =
      liveLabelAt (extractionPrefixExtension N h c.val).1 i)
    (n : ℕ) (hn : n ≤ N + 1) (hcn : c.val + 1 ≤ n) (d : ℕ)
    (hd : (extractionRun N h n).detached = some d) :
    ancestorLabel N (extractionPrefixExtension N h) q r n = d := by
  classical
  induction n, hcn using Nat.le_induction with
  | base =>
    have hev' : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 = .inr (.inr (i, x)) := by
      simpa only [extractionPrefixExtension_prefix N h (c.val + 1) c.isLt] using hev
    rw [extractionRun_succ N h c.val c.isLt] at hd
    simp only [extractionStep, hev'] at hd
    have hqd := ancestorLabel_no_split_prefix N (extractionPrefixExtension N h) c.val
      (fun l hl => hother l (by omega)) q leftBoundaryProbe r
    simp only [ancestorLabel, hev, ancestorStep, hi, true_and, hqd, hr, ↓reduceIte,
      not_lt.mpr hq]
    simpa only [extractionPrefixExtension_prefix N h c.val c.isLt.le] using Option.some.inj hd
  | succ n hcn ih =>
    have hlt : n < N + 1 := by omega
    have hother' := hother n (by omega)
    rw [extractionPrefixExtension_prefix N h (n + 1) hn] at hother'
    rw [extractionRun_succ N h n hlt] at hd
    rcases hother' with he | ⟨ij, he⟩
    · simp only [extractionStep, he] at hd
      change ancestorStep (extractionPrefixExtension N h n).1
        (extractionPrefixExtension N h (n + 1)).2.2 q
        (ancestorLabel N (extractionPrefixExtension N h) q r n) = d
      rw [extractionPrefixExtension_prefix N h (n + 1) hn, he]
      exact ih (by omega) hd
    · simp only [extractionStep, he] at hd
      split at hd
      · cases hd
      · rename_i hmiss
        have hrec := ih (by omega) hd
        have hnot : ¬ (d = liveLabelAt (h ⟨n, Finset.mem_Iic.mpr hlt.le⟩).1 ij.1 ∨
            d = liveLabelAt (h ⟨n, Finset.mem_Iic.mpr hlt.le⟩).1 ij.2) := by
          intro hhit
          exact hmiss ⟨d, hd, hhit⟩
        simp only [ancestorLabel, extractionPrefixExtension_prefix N h n hlt.le,
          extractionPrefixExtension_prefix N h (n + 1) hn, he, ancestorStep, hrec,
          hnot, ↓reduceIte]
        split_ifs <;> rfl

theorem oneSplitPrefix_detached_disappears (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hev : (extractionPrefixExtension N h (c.val + 1)).2.2 = .inr (.inr (i, x))) :
    ∃ l : ℕ, c.val < l ∧ l < N + 1 ∧ ∃ d : ℕ,
      (extractionRun N h l).detached = some d ∧
      (extractionRun N h (l + 1)).detached = none := by
  classical
  have hcut : (extractionRun N h (c.val + 1)).detached =
      some (extractionPrefixExtension N h c.val).1.2.1.succ := by
    rw [extractionRun_succ N h c.val c.isLt]
    have hev' : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 = .inr (.inr (i, x)) := by
      simpa only [extractionPrefixExtension_prefix N h (c.val + 1) c.isLt] using hev
    simp only [extractionStep, hev', extractionPrefixExtension_prefix N h c.val c.isLt.le]
  have hex : ∃ k, c.val + 1 ≤ k ∧ (extractionRun N h k).detached = none :=
    ⟨N + 1, c.isLt, (extractionRun_terminal_inventory N h hs).1⟩
  have hspec := Nat.find_spec hex
  have hlast : Nat.find hex ≤ N + 1 := Nat.find_min' hex
    ⟨c.isLt, (extractionRun_terminal_inventory N h hs).1⟩
  have hstrict : c.val + 1 < Nat.find hex := by
    by_contra hn
    have he : Nat.find hex = c.val + 1 := by omega
    rw [he, hcut] at hspec
    cases hspec.2
  let l := Nat.find hex - 1
  have hl : l + 1 = Nat.find hex := by dsimp [l]; omega
  have hnone : (extractionRun N h l).detached ≠ none := by
    intro hd
    exact Nat.find_min hex (show l < Nat.find hex by omega) ⟨by omega, hd⟩
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hnone
  refine ⟨l, by omega, by omega, d, hd, ?_⟩
  simpa only [hl] using hspec.2

end Rhone.Coalescent.SmcPrime
