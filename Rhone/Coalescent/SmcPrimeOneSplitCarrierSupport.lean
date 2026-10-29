/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeOneSplitRightCut
public import Rhone.Coalescent.SmcSupport.SingleCutReachableExposure
/-! # Finite prefix carrier and zero- or one-split successor support -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess SmcSupport
theorem oneSplitPrefix_ancestorCarried (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (q : GenomicProbe) (j : Fin N)
    (k : ℕ) (hk : k ≤ N + 1) :
    ancestorCarried (extractionPrefixExtension N h k).1 (q.val : ℝ)
      (ancestorLabel N (extractionPrefixExtension N h) q j k) := by
  induction k with
  | zero =>
    simp only [ancestorLabel, extractionPrefixExtension_prefix N h 0 (by omega), hs.1]
    exact initial_ancestorCarried N q j
  | succ k ih =>
    have hb : k ≤ N + 1 := by omega
    have hl : k < N + 1 := by omega
    let ω := extractionPrefixExtension N h
    have ht : ARGTransition (ω k, ω (k + 1)) := by
      simp only [ω, extractionPrefixExtension_prefix N h k hb,
        extractionPrefixExtension_prefix N h (k + 1) hk]
      exact hs.2.2.1 ⟨k, hl⟩
    have hv : Valid (ω k).1 := by
      dsimp only [ω]
      rw [extractionPrefixExtension_prefix N h k hb]
      exact hs.2.1 _
    obtain ⟨c, hsplit, hcoal⟩ := hs.2.2.2.2.1
    by_cases he : (⟨k, hl⟩ : Fin (N + 1)) = c
    · have hm : (ω (k + 1)).2.2 ∈ splitSet := by
        dsimp only [ω]
        rw [extractionPrefixExtension_prefix N h (k + 1) hk]
        simpa only [← he] using hsplit
      obtain ⟨i, x, _, _, hev, hn, _⟩ := ht.split_case hv hm
      change ancestorCarried (ω (k + 1)).1 (q.val : ℝ)
        (ancestorStep (ω k).1 (ω (k + 1)).2.2 q (ancestorLabel N ω q j k))
      rw [hn, hev, ancestorCarried_atTime]
      exact splitSuccessor_ancestorCarried (ω k).1 hv q _ (ih hb) i x
    · have hm : (ω (k + 1)).2.2 ∈ coalSet := by
        dsimp only [ω]
        rw [extractionPrefixExtension_prefix N h (k + 1) hk]
        exact hcoal ⟨k, hl⟩ he
      obtain ⟨i, u, hiu, hev, hn, _⟩ := ht.coal_case hm
      change ancestorCarried (ω (k + 1)).1 (q.val : ℝ)
        (ancestorStep (ω k).1 (ω (k + 1)).2.2 q (ancestorLabel N ω q j k))
      rw [hn, hev, ancestorCarried_atTime]
      exact coalSuccessor_ancestorCarried (ω k).1 hv q _ (ih hb) i u hiu

private theorem other_pairs (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hev : (extractionPrefixExtension N h (c.val + 1)).2.2 = .inr (.inr (i, x))) :
    ∀ l : Fin (N + 1), l ≠ c →
      (extractionPrefixExtension N h (l.val + 1)).2.2 ∈ coalSet := by
  obtain ⟨d, hsplit, hcoal⟩ := hs.2.2.2.2.1
  have hcd : c = d := by
    by_contra hne
    have hc := hcoal c hne
    rw [← extractionPrefixExtension_prefix N h (c.val + 1) (by omega), hev] at hc
    cases hc
  intro l hl
  rw [extractionPrefixExtension_prefix N h (l.val + 1) (by omega)]
  exact hcoal l (fun he => hl (he.trans hcd.symm))

theorem oneSplitPrefix_reachable (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (c : Fin (N + 1)) (i : ℕ) (x : ℝ)
    (hev : (extractionPrefixExtension N h (c.val + 1)).2.2 = .inr (.inr (i, x)))
    (k : ℕ) (hk : k ≤ N + 1) :
    if k ≤ c.val then ZeroSplitReachable (extractionPrefixExtension N h k).1
    else OneSplitReachable x (extractionPrefixExtension N h k).1 := by
  have hother := other_pairs N h hs c i x hev
  induction k with
  | zero =>
    simp only [Nat.zero_le, ite_true, extractionPrefixExtension_prefix N h 0 (by omega), hs.1]
    exact ZeroSplitReachable.initial N
  | succ k ih =>
    have hb : k ≤ N + 1 := by omega
    have hl : k < N + 1 := by omega
    let ω := extractionPrefixExtension N h
    have ht : ARGTransition (ω k, ω (k + 1)) := by
      simp only [ω, extractionPrefixExtension_prefix N h k hb,
        extractionPrefixExtension_prefix N h (k + 1) hk]
      exact hs.2.2.1 ⟨k, hl⟩
    have hv : Valid (ω k).1 := by
      dsimp only [ω]
      rw [extractionPrefixExtension_prefix N h k hb]
      exact hs.2.1 _
    have hprev := ih hb
    by_cases he : k = c.val
    · have hm : (ω (k + 1)).2.2 ∈ splitSet := by
        simp only [ω, he, hev, splitSet, Set.mem_ofPred_eq]
      obtain ⟨v, y, _, _, hvy, hn, _⟩ := ht.split_case hv hm
      have hevent : (ω (k + 1)).2.2 = .inr (.inr (i, x)) := by
        simpa only [ω, he] using hev
      have hxy : y = x :=
        congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj (hvy.symm.trans hevent)))
      subst y
      have hz : ZeroSplitReachable (ω k).1 := by
        simpa only [ite_eq_left (show k ≤ c.val by omega)] using hprev
      rw [ite_eq_right (show ¬ k + 1 ≤ c.val by omega)]
      change OneSplitReachable x (ω (k + 1)).1
      rw [hn]
      exact OneSplitReachable.clock (OneSplitReachable.split hz v) _
    · have hne : (⟨k, hl⟩ : Fin (N + 1)) ≠ c := by
        intro hc
        exact he (congrArg Fin.val hc)
      have hm : (ω (k + 1)).2.2 ∈ coalSet := hother ⟨k, hl⟩ hne
      obtain ⟨v, u, _, _, hn, _⟩ := ht.coal_case hm
      by_cases hbefore : k ≤ c.val
      · have hz : ZeroSplitReachable (ω k).1 := by
          simpa only [ite_eq_left hbefore] using hprev
        rw [ite_eq_left (show k + 1 ≤ c.val by omega)]
        change ZeroSplitReachable (ω (k + 1)).1
        rw [hn]
        exact ZeroSplitReachable.clock (ZeroSplitReachable.coal hz v u) _
      · have ho : OneSplitReachable x (ω k).1 := by
          simpa only [ite_eq_right hbefore] using hprev
        rw [ite_eq_right (show ¬ k + 1 ≤ c.val by omega)]
        change OneSplitReachable x (ω (k + 1)).1
        rw [hn]
        exact OneSplitReachable.clock (OneSplitReachable.coal ho v u) _
end Rhone.Coalescent.SmcPrime
