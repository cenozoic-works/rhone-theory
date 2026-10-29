/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitPrefixSupport

/-! # Pair and cut cases of supported ARG transitions -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem ARGTransition.coal_case {pre next : AugmentedState}
    (h : ARGTransition (pre, next)) (he : next.2.2 ∈ coalSet) :
    ∃ i j : Fin pre.1.2.2.1, i.val < j.val ∧
      next.2.2 = .inr (.inl (i.val, j.val)) ∧
      next.1 = atTime next.1.1 (coalSuccessor pre.1 i j) ∧ pre.1.1 < next.1.1 := by
  classical
  rcases h with hk | ⟨_, k, hk, hev, _, _, _, _⟩
  · unfold KingmanTransition at hk
    split_ifs at hk with hm
    · obtain ⟨ij, hij, hj, hev, hnext, ht⟩ := hk
      have hi : ij.1 < pre.1.2.2.1 := hij.trans hj
      refine ⟨⟨ij.1, hi⟩, ⟨ij.2, hj⟩, hij, hev, ?_, ht⟩
      simpa only [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using hnext
    · obtain ⟨_, hev⟩ := hk
      rw [hev] at he
      cases he
  · rw [hev] at he
    cases he

theorem ARGTransition.split_case {pre next : AugmentedState}
    (h : ARGTransition (pre, next)) (hs : Valid pre.1) (he : next.2.2 ∈ splitSet) :
    ∃ i : Fin pre.1.2.2.1, ∃ x : ℝ, 0 < x ∧ x < 1 ∧
      next.2.2 = .inr (.inr (i.val, x)) ∧
      next.1 = atTime next.1.1 (splitSuccessor pre.1 i x) ∧ pre.1.1 < next.1.1 := by
  classical
  rcases h with hk | ⟨_, k, hk, hev, hlo, hhi, hnext, ht⟩
  · unfold KingmanTransition at hk
    split_ifs at hk
    · obtain ⟨_, _, _, hev, _, _⟩ := hk
      rw [hev] at he
      cases he
    · rw [hk.2] at he
      cases he
  · let x := (genealogyEventCode next.2.2).2.2.2
    let i : Fin pre.1.2.2.1 := ⟨k, hk⟩
    have hlo' : hullLo (pre.1.2.2.2 i).2 < x := by
      simpa only [lineageHullEndpoint, dite_eq_left hk, Bool.false_eq_true, ite_false] using hlo
    have hhi' : x < hullHi (pre.1.2.2.2 i).2 := by
      simpa only [lineageHullEndpoint, dite_eq_left hk, ite_true] using hhi
    have hb := SmcSupport.hull_bounds _ (hs.2.1 i)
    refine ⟨i, x, hb.1.trans_lt hlo', hhi'.trans_le hb.2.2, hev, ?_, ht⟩
    simpa only [splitSuccessorNat, dite_eq_left hk] using hnext

end Rhone.Coalescent.SmcPrime
