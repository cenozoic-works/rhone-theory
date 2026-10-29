/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitDetachedRepresentative

/-! # Attachment data of a supported one-split prefix -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem oneSplitPrefix_attachment_data_tracked (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hi : i < (extractionPrefixExtension N h c.val).1.2.2.1)
    (hev : (extractionPrefixExtension N h (c.val + 1)).2.2 = .inr (.inr (i, x)))
    (hother : ∀ l, l ≠ c.val → CoalOrStop (extractionPrefixExtension N h (l + 1)).2.2)
    (r : Fin N)
    (hr : ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe r c.val =
      liveLabelAt (extractionPrefixExtension N h c.val).1 i) :
    let ω := extractionPrefixExtension N h
    ∃ l : ℕ, c.val < l ∧ l < N + 1 ∧ ∃ ij : ℕ × ℕ, ∃ d : Fin N,
      (ω (l + 1)).2.2 = .inr (.inl ij) ∧
      ij.1 < ij.2 ∧ ij.2 < (ω l).1.2.2.1 ∧
      (∃ a : ℕ, (extractionRun N h l).detached = some a ∧
        (extractionRun N h (l + 1)).detached = none) ∧
      ∀ q : GenomicProbe, x ≤ (q.val : ℝ) →
        (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.1 ∧
          ancestorLabel N ω leftBoundaryProbe d l = liveLabelAt (ω l).1 ij.2) ∨
        (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.2 ∧
          ancestorLabel N ω leftBoundaryProbe d l = liveLabelAt (ω l).1 ij.1) := by
  classical
  dsimp only
  obtain ⟨l, hcl, hl, a, ha, hanext⟩ := oneSplitPrefix_detached_disappears N h hs c i x hev
  have hother' := hother l (by omega)
  rw [extractionPrefixExtension_prefix N h (l + 1) hl] at hother'
  have hcoal : (h ⟨l + 1, Finset.mem_Iic.mpr hl⟩).2.2 ∈ coalSet := by
    rcases hother' with he | ⟨ij, he⟩
    · rw [extractionRun_succ N h l hl] at hanext
      simp only [extractionStep, he] at hanext
      rw [ha] at hanext
      cases hanext
    · rw [he]
      trivial
  obtain ⟨u, v, huv, hpair, _, _⟩ := (hs.2.2.1 ⟨l, hl⟩).coal_case hcoal
  let pre := (h ⟨l, Finset.mem_Iic.mpr hl.le⟩).1
  have hu_lt : u.val < pre.2.2.1 := u.isLt
  have hv_lt : v.val < pre.2.2.1 := v.isLt
  have hlu : liveLabelAt pre u.val = (pre.2.2.2 u).1 := by
    simp only [liveLabelAt, dite_eq_left hu_lt]
    rfl
  have hlv : liveLabelAt pre v.val = (pre.2.2.2 v).1 := by
    simp only [liveLabelAt, dite_eq_left hv_lt]
    rfl
  have hhit : a = (pre.2.2.2 u).1 ∨ a = (pre.2.2.2 v).1 := by
    by_contra hn
    have hmiss : ¬ ∃ b, (extractionRun N h l).detached = some b ∧
        (b = liveLabelAt pre u.val ∨ b = liveLabelAt pre v.val) := by
      rintro ⟨b, hb, hhit⟩
      have hab : a = b := Option.some.inj (ha.symm.trans hb)
      subst b
      exact hn (by simpa only [hlu, hlv] using hhit)
    rw [extractionRun_succ N h l hl] at hanext
    dsimp only [pre] at hmiss
    simp only [extractionStep, hpair, hmiss, ↓reduceIte] at hanext
    rw [ha] at hanext
    cases hanext
  have hpre := hs.2.1 ⟨l, Finset.mem_Iic.mpr hl.le⟩
  have hne : (pre.2.2.2 u).1 ≠ (pre.2.2.2 v).1 := by
    intro he
    have heuv : u = v := hpre.2.2.2 he
    have := congrArg Fin.val heuv
    omega
  have hinv := (extractionRun_inventory N h hs l hl.le).2.1
  have hright (q : GenomicProbe) (hq : x ≤ (q.val : ℝ)) :
      ancestorLabel N (extractionPrefixExtension N h) q r l = a :=
    extractionRun_detached_right N h c i x hi hev hother q hq r hr l hl.le (by omega) a ha
  have hleft (j : Fin pre.2.2.1) (hj : a ≠ (pre.2.2.2 j).1) :
      ∃ d : Fin N, ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe d l =
        (pre.2.2.2 j).1 := by
    rcases hinv.2.1 j with ⟨d, hd⟩ | hdet
    · exact ⟨d, by rw [← extractionRun_argLabels N h l hl.le d]; exact hd⟩
    · exact False.elim (hj (Option.some.inj (ha.symm.trans hdet)))
  rcases hhit with hu | hv
  · obtain ⟨d, hd⟩ := hleft v (by rw [hu]; exact hne)
    refine ⟨l, hcl, hl, (u.val, v.val), d, ?_, huv, ?_, ⟨a, ha, hanext⟩, ?_⟩
    · rw [extractionPrefixExtension_prefix N h (l + 1) hl]
      exact hpair
    · rw [extractionPrefixExtension_prefix N h l hl.le]
      exact v.isLt
    · intro q hq
      apply Or.inl
      rw [extractionPrefixExtension_prefix N h l hl.le]
      change _ = liveLabelAt pre u.val ∧ _ = liveLabelAt pre v.val
      rw [hlu, hlv]
      exact ⟨(hright q hq).trans hu, hd⟩
  · obtain ⟨d, hd⟩ := hleft u (by rw [hv]; exact Ne.symm hne)
    refine ⟨l, hcl, hl, (u.val, v.val), d, ?_, huv, ?_, ⟨a, ha, hanext⟩, ?_⟩
    · rw [extractionPrefixExtension_prefix N h (l + 1) hl]
      exact hpair
    · rw [extractionPrefixExtension_prefix N h l hl.le]
      exact v.isLt
    · intro q hq
      apply Or.inr
      rw [extractionPrefixExtension_prefix N h l hl.le]
      change _ = liveLabelAt pre v.val ∧ _ = liveLabelAt pre u.val
      rw [hlu, hlv]
      exact ⟨(hright q hq).trans hv, hd⟩

theorem oneSplitPrefix_attachment_data (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hi : i < (extractionPrefixExtension N h c.val).1.2.2.1)
    (hev : (extractionPrefixExtension N h (c.val + 1)).2.2 = .inr (.inr (i, x)))
    (hother : ∀ l, l ≠ c.val → CoalOrStop (extractionPrefixExtension N h (l + 1)).2.2)
    (r : Fin N)
    (hr : ancestorLabel N (extractionPrefixExtension N h) leftBoundaryProbe r c.val =
      liveLabelAt (extractionPrefixExtension N h c.val).1 i) :
    let ω := extractionPrefixExtension N h
    ∃ l : ℕ, c.val < l ∧ l < N + 1 ∧ ∃ ij : ℕ × ℕ, ∃ d : Fin N,
      (ω (l + 1)).2.2 = .inr (.inl ij) ∧
      ij.1 < ij.2 ∧ ij.2 < (ω l).1.2.2.1 ∧
      ∀ q : GenomicProbe, x ≤ (q.val : ℝ) →
        (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.1 ∧
          ancestorLabel N ω leftBoundaryProbe d l = liveLabelAt (ω l).1 ij.2) ∨
        (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.2 ∧
          ancestorLabel N ω leftBoundaryProbe d l = liveLabelAt (ω l).1 ij.1) := by
  obtain ⟨l, hcl, hl, ij, d, hev', hij, hj, _, hchildren⟩ :=
    oneSplitPrefix_attachment_data_tracked N h hs c i x hi hev hother r hr
  exact ⟨l, hcl, hl, ij, d, hev', hij, hj, hchildren⟩

end Rhone.Coalescent.SmcPrime
