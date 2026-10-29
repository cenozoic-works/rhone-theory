/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitRightClades
public import Rhone.Coalescent.SmcPrimeOneSplitTerminalInventory

/-! # Cut data and right-sample ancestry of one-split prefixes -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem coalOrStop_of_mem_coalSet (e : Event) (he : e ∈ coalSet) : CoalOrStop e := by
  cases e with
  | inl u => cases he
  | inr a =>
    cases a with
    | inl ij => exact Or.inr ⟨ij, rfl⟩
    | inr ix => cases he

theorem extractionPrefixExtension_no_other_split (N : ℕ) (h : ARGPrefix (N + 1))
    (c : Fin (N + 1))
    (hcoal : ∀ k : Fin (N + 1), k ≠ c →
      (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).2.2 ∈ coalSet)
    (l : ℕ) (hl : l ≠ c.val) :
    CoalOrStop (extractionPrefixExtension N h (l + 1)).2.2 := by
  by_cases hn : l + 1 ≤ N + 1
  · rw [extractionPrefixExtension_prefix N h (l + 1) hn]
    apply coalOrStop_of_mem_coalSet
    apply hcoal ⟨l, by omega⟩
    intro he
    exact hl (congrArg Fin.val he)
  · simp only [extractionPrefixExtension, dite_eq_right hn]
    exact Or.inl rfl

theorem oneSplitPrefix_cut_data (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    let ω := extractionPrefixExtension N h
    ∃ c : Fin (N + 1), ∃ i : ℕ, ∃ x : ℝ, ∃ r : Fin N,
      0 < x ∧ x < 1 ∧ i < (ω c.val).1.2.2.1 ∧
      (ω (c.val + 1)).2.2 = .inr (.inr (i, x)) ∧
      (∀ l, l ≠ c.val → CoalOrStop (ω (l + 1)).2.2) ∧
      ancestorLabel N ω leftBoundaryProbe r c.val = liveLabelAt (ω c.val).1 i := by
  dsimp only
  obtain ⟨c, hsplit, hcoal⟩ := hs.2.2.2.2.1
  have hc : c.val ≤ N + 1 := c.isLt.le
  have hcs : c.val + 1 ≤ N + 1 := c.isLt
  have hpre := hs.2.1 ⟨c.val, Finset.mem_Iic.mpr hc⟩
  obtain ⟨i, x, hx0, hx1, hev, _, _⟩ := (hs.2.2.1 c).split_case hpre hsplit
  have hinv := (extractionRun_inventory N h hs c.val hc).2.1
  have hnone := extractionRun_detached_before_split N h c hcoal c.val le_rfl
  obtain ⟨r, hr⟩ : ∃ r : Fin N,
      (extractionRun N h c.val).argLabels r =
        ((h ⟨c.val, Finset.mem_Iic.mpr hc⟩).1.2.2.2 i).1 := by
    rcases hinv.2.1 i with hr | hd
    · exact hr
    · rw [hnone] at hd
      cases hd
  refine ⟨c, i.val, x, r, hx0, hx1, ?_, ?_, ?_, ?_⟩
  · rw [extractionPrefixExtension_prefix N h c.val hc]
    exact i.isLt
  · rw [extractionPrefixExtension_prefix N h (c.val + 1) hcs]
    exact hev
  · exact extractionPrefixExtension_no_other_split N h c hcoal
  · rw [extractionPrefixExtension_prefix N h c.val hc, liveLabelAt,
      dite_eq_left i.isLt, ← extractionRun_argLabels N h c.val hc r]
    exact hr

theorem oneSplitPrefix_right_ancestry (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    let ω := extractionPrefixExtension N h
    ∃ c : Fin (N + 1), ∃ i : ℕ, ∃ x : ℝ, ∃ r : Fin N,
      0 < x ∧ x < 1 ∧ (ω (c.val + 1)).2.2 = .inr (.inr (i, x)) ∧
      ∀ q : GenomicProbe, x ≤ (q.val : ℝ) → ∀ j : Fin N, ∀ k : ℕ, c.val + 1 ≤ k →
        ancestorLabel N ω q j k =
          if ancestorLabel N ω leftBoundaryProbe j c.val = liveLabelAt (ω c.val).1 i
          then ancestorLabel N ω q r k else ancestorLabel N ω leftBoundaryProbe j k := by
  obtain ⟨c, i, x, r, hx0, hx1, hi, hev, hother, hr⟩ := oneSplitPrefix_cut_data N h hs
  refine ⟨c, i, x, r, hx0, hx1, hev, ?_⟩
  intro q hq j k hk
  exact ancestorLabel_single_split_right N (extractionPrefixExtension N h) c.val i x
    hx0 hi hev (fun l hl => hother l (by omega)) (fun l hl => hother l (by omega))
    q hq r hr j k hk

end Rhone.Coalescent.SmcPrime
