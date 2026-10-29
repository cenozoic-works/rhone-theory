/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanUIDs

/-! # Chronological fresh lineage identifiers determine the recorded birth times -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem kingman_pair_birth_time (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k a : ℕ) (hk : k < N) :
    pairBirthTime ω k a =
      if N ≤ a ∧ a < N + k then (ω (a - N + 1)).1.1 else 0 := by
  induction k with
  | zero =>
    have hc : ¬ (N ≤ a ∧ a < N + 0) := by omega
    simp only [pairBirthTime, ite_eq_right hc]
  | succ k ih =>
    have hk0 : k < N := by omega
    have hc := kingman_path_count N ω hinit hstep k hk0
    have hm : 2 ≤ (ω k).1.2.2.1 := by omega
    obtain ⟨ij, hij, hj, hev, _, _⟩ := (ite_eq_left hm).mp (hstep k)
    change (ω (k + 1)).2.2 = .inr (.inl ij) at hev
    change ij.2 < (ω k).1.2.2.1 at hj
    have hf := kingman_path_fresh N ω hinit hstep k hk0
    simp only [pairBirthTime, hev, hij, hj, true_and, hf]
    by_cases ha : a = N + k
    · subst a
      have hcond : N ≤ N + k ∧ N + k < N + (k + 1) := by omega
      have heq : N + k - N + 1 = k + 1 := by omega
      simp only [ite_true, ite_eq_left hcond, heq]
    · have hcond : (N ≤ a ∧ a < N + (k + 1)) ↔ (N ≤ a ∧ a < N + k) := by omega
      rw [ite_eq_right ha, ih hk0]
      simp only [hcond]

end Rhone.Coalescent.SmcPrime
