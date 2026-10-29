/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitObservation

/-! # Event accounting for unrestricted ARG paths: splits, coalescences, and idle steps -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem ARGTransition.count_cases {pre next : AugmentedState} (ht : ARGTransition (pre, next)) :
    (next.2.2 = .inl () ∧ next.1 = pre.1 ∧ pre.1.2.2.1 ≤ 1) ∨
      (next.2.2 ∈ coalSet ∧ 2 ≤ pre.1.2.2.1 ∧ next.1.2.2.1 + 1 = pre.1.2.2.1) ∨
      (next.2.2 ∈ splitSet ∧ 2 ≤ pre.1.2.2.1 ∧ next.1.2.2.1 = pre.1.2.2.1 + 1) := by
  classical
  rcases ht with hk | ⟨hm, i, hi, hev, _, _, hn, _⟩
  · have hc := hk.count
    by_cases hm : 2 ≤ pre.1.2.2.1
    · obtain ⟨ij, _, _, he, _, _⟩ := (ite_eq_left hm).mp hk
      rw [ite_eq_left hm] at hc
      dsimp only at hc
      exact Or.inr (Or.inl ⟨by rw [he]; trivial, hm, by omega⟩)
    · obtain ⟨hn, he⟩ := (ite_eq_right hm).mp hk
      exact Or.inl ⟨he, hn, by omega⟩
  · apply Or.inr ∘ Or.inr
    have hc := splitSuccessor_count pre.1 ⟨i, hi⟩ (genealogyEventCode next.2.2).2.2.2
    refine ⟨by rw [hev]; trivial, hm, ?_⟩
    rw [hn]
    simpa only [atTime, splitSuccessorNat, dite_eq_left hi] using hc

noncomputable def finiteARGSplitCount (ω : EventPath) (k : ℕ) : ℕ := by
  classical
  exact ∑ l ∈ Finset.range k, if (ω (l + 1)).2.2 ∈ splitSet then 1 else 0

noncomputable def finiteARGIdleCount (ω : EventPath) (k : ℕ) : ℕ := by
  classical
  exact ∑ l ∈ Finset.range k, if (ω (l + 1)).2.2 = .inl () then 1 else 0

theorem arg_path_count_balance (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hstep : ∀ k, ARGTransition (ω k, ω (k + 1)))
    (k : ℕ) :
    (ω k).1.2.2.1 + k = N + 2 * finiteARGSplitCount ω k + finiteARGIdleCount ω k := by
  classical
  induction k with
  | zero => simp [finiteARGSplitCount, finiteARGIdleCount, hinit, initialState]
  | succ k ih =>
    have hs : finiteARGSplitCount ω (k + 1) = finiteARGSplitCount ω k +
        if (ω (k + 1)).2.2 ∈ splitSet then 1 else 0 := by
      exact Finset.sum_range_succ _ k
    have hi : finiteARGIdleCount ω (k + 1) = finiteARGIdleCount ω k +
        if (ω (k + 1)).2.2 = .inl () then 1 else 0 := by
      exact Finset.sum_range_succ _ k
    rw [hs, hi]
    rcases (hstep k).count_cases with ⟨he, hn, _⟩ | ⟨he, _, hc⟩ | ⟨he, _, hc⟩
    · simp only [he, splitSet, Set.mem_ofPred_eq, ite_false, ite_true, hn]
      omega
    · have hns : (ω (k + 1)).2.2 ∉ splitSet := by
        cases hv : (ω (k + 1)).2.2 with
        | inl u => rw [hv] at he; cases he
        | inr a => cases a with
          | inl ij => simp [splitSet]
          | inr ix => rw [hv] at he; cases he
      have hni : (ω (k + 1)).2.2 ≠ .inl () := by intro hv; rw [hv] at he; cases he
      simp only [hns, hni, ite_false]
      omega
    · have hni : (ω (k + 1)).2.2 ≠ .inl () := by intro hv; rw [hv] at he; cases he
      simp only [he, hni, ite_true, ite_false]
      omega

theorem arg_path_count_le_one_later (ω : EventPath)
    (hstep : ∀ k, ARGTransition (ω k, ω (k + 1))) (n m : ℕ) (hnm : n ≤ m)
    (hn : (ω n).1.2.2.1 ≤ 1) : (ω m).1.2.2.1 ≤ 1 := by
  induction m, hnm using Nat.le_induction with
  | base => exact hn
  | succ m hnm ih =>
    rcases (hstep m).count_cases with ⟨_, he, _⟩ | ⟨_, hm, _⟩ | ⟨_, hm, _⟩
    · rwa [he]
    · omega
    · omega

theorem arg_path_count_positive (N : ℕ) (hN : 0 < N) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hstep : ∀ k, ARGTransition (ω k, ω (k + 1)))
    (k : ℕ) : 0 < (ω k).1.2.2.1 := by
  induction k with
  | zero => simpa only [hinit, initialState] using hN
  | succ k ih =>
    rcases (hstep k).count_cases with ⟨_, he, _⟩ | ⟨_, hm, hc⟩ | ⟨_, _, hc⟩
    · rwa [he]
    · omega
    · omega

end Rhone.Coalescent.SmcPrime
