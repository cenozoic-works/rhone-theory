/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitAttachmentWitness
public import Rhone.Coalescent.SmcPrimeOneSplitAttachmentFields

/-! # Attachment target of the extracted skeleton -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem oneSplitPrefix_attachment_target (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hx1 : x < 1)
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
      (extractOneSplitSkeleton N h).2.2.2.2 =
        ((ω (l + 1)).1.1, extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j l)
          (ancestorLabel N ω leftBoundaryProbe d l)) ∧
      ∀ q : GenomicProbe, x ≤ (q.val : ℝ) →
        (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.1 ∧
          ancestorLabel N ω leftBoundaryProbe d l = liveLabelAt (ω l).1 ij.2) ∨
        (ancestorLabel N ω q r l = liveLabelAt (ω l).1 ij.2 ∧
          ancestorLabel N ω leftBoundaryProbe d l = liveLabelAt (ω l).1 ij.1) := by
  classical
  dsimp only
  obtain ⟨l, hcl, hl, ij, d, hpair, hij, hj, hdet, hchildren⟩ :=
    oneSplitPrefix_attachment_data_tracked N h hs c i x hi hev hother r hr
  obtain ⟨a, ha, hanext⟩ := hdet
  let ω := extractionPrefixExtension N h
  have hleft : ancestorLabel N ω leftBoundaryProbe d l ≠ a := by
    rw [← extractionRun_argLabels N h l hl.le d]
    exact ((extractionRun_inventory N h hs l hl.le).2.1.2.2 a ha).2 d
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (max_lt (show (0:ℝ)<1 by norm_num) hx1)
  let q' : GenomicProbe := ⟨q, by exact_mod_cast (le_max_left 0 x).trans hq0.le,
    by exact_mod_cast hq1⟩
  have hqx : x ≤ (q'.val : ℝ) := (le_max_right 0 x).trans hq0.le
  have hright : ancestorLabel N ω q' r l = a :=
    extractionRun_detached_right N h c i x hi hev hother q' hqx r hr l hl.le
      (by omega) a ha
  have hhit : ∃ b, (extractionRun N h l).detached = some b ∧
      (b = liveLabelAt (ω l).1 ij.1 ∨ b = liveLabelAt (ω l).1 ij.2) := by
    refine ⟨a, ha, ?_⟩
    rcases hchildren q' hqx with hp | hp
    · exact Or.inl (hright.symm.trans hp.1)
    · exact Or.inr (hright.symm.trans hp.1)
  have htarget : (if (extractionRun N h l).detached = some (liveLabelAt (ω l).1 ij.1)
        then liveLabelAt (ω l).1 ij.2 else liveLabelAt (ω l).1 ij.1) =
      ancestorLabel N ω leftBoundaryProbe d l := by
    rcases hchildren q' hqx with hp | hp
    · have he : a = liveLabelAt (ω l).1 ij.1 := hright.symm.trans hp.1
      rw [ha, he, ite_eq_left rfl]
      exact hp.2.symm
    · have hne : a ≠ liveLabelAt (ω l).1 ij.1 := by
        intro he
        exact hleft (hp.2.trans he.symm)
      rw [ha, ite_eq_right (fun he => hne (Option.some.inj he))]
      exact hp.2.symm
  have hfields := extractOneSplitSkeleton_attachment_fields N h l hl ij hpair hhit
    (fun m hm => hother m (by omega))
  change (extractOneSplitSkeleton N h).2.2.2.2 =
    ((ω (l + 1)).1.1,
      extractionClade (fun j => ancestorLabel N ω leftBoundaryProbe j l) _) at hfields
  rw [htarget] at hfields
  exact ⟨l, hcl, hl, ij, d, hpair, hij, hj, ⟨a, ha, hanext⟩, hfields, hchildren⟩

end Rhone.Coalescent.SmcPrime
