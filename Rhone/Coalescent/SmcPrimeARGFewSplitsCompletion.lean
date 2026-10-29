/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGPathCount

/-! # ARG paths with at most one split: stopping event and terminal prefix -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem arg_path_splitCount_le_one (ω : EventPath)
    (huniq : ∀ i j, (ω (i + 1)).2.2 ∈ splitSet → (ω (j + 1)).2.2 ∈ splitSet → i = j)
    (k : ℕ) : finiteARGSplitCount ω k ≤ 1 := by
  classical
  have hc : ((Finset.range k).filter (fun l => (ω (l + 1)).2.2 ∈ splitSet)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact huniq i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  simpa [finiteARGSplitCount, ← Finset.sum_filter] using hc

theorem arg_path_stopped_event (ω : EventPath)
    (hstep : ∀ k, ARGTransition (ω k, ω (k + 1))) (n k : ℕ) (hnk : n ≤ k)
    (hn : (ω n).1.2.2.1 ≤ 1) : (ω (k + 1)).2.2 = .inl () := by
  have hk := arg_path_count_le_one_later ω hstep n k hnk hn
  rcases (hstep k).count_cases with ⟨he, _, _⟩ | ⟨_, hm, _⟩ | ⟨_, hm, _⟩
  · exact he
  · omega
  · omega

theorem arg_path_few_splits_terminal (N : ℕ) (hN : 0 < N) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N) (hstep : ∀ k, ARGTransition (ω k, ω (k + 1)))
    (huniq : ∀ i j, (ω (i + 1)).2.2 ∈ splitSet → (ω (j + 1)).2.2 ∈ splitSet → i = j) :
    (ω (N + 1)).1.2.2.1 = 1 := by
  classical
  have hp := arg_path_count_positive N hN ω hinit hstep (N + 1)
  suffices hl : (ω (N + 1)).1.2.2.1 ≤ 1 by omega
  by_contra hn
  have hactive : 1 < (ω (N + 1)).1.2.2.1 := by omega
  have hnoidle (l : ℕ) (hl : l < N + 1) : (ω (l + 1)).2.2 ≠ .inl () := by
    intro he
    have hc : (ω (l + 1)).1.2.2.1 ≤ 1 := by
      rcases (hstep l).count_cases with ⟨_, hnxt, hc⟩ | ⟨hc, _, _⟩ | ⟨hc, _, _⟩
      · rwa [hnxt]
      · rw [he] at hc; cases hc
      · rw [he] at hc; cases hc
    have hfinal := arg_path_count_le_one_later ω hstep (l + 1) (N + 1) hl hc
    omega
  have hstops : finiteARGIdleCount ω (N + 1) = 0 := by
    unfold finiteARGIdleCount
    apply Finset.sum_eq_zero
    intro l hl
    rw [ite_eq_right (hnoidle l (Finset.mem_range.mp hl))]
  have hbal := arg_path_count_balance N ω hinit hstep (N + 1)
  have hsplit := arg_path_splitCount_le_one ω huniq (N + 1)
  omega

end Rhone.Coalescent.SmcPrime
