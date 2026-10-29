/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanPrefix

/-! # Exact stopped continuation of finite Kingman histories -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

noncomputable def kingmanCompletion (N : ℕ) (h : KingmanHistory N) : EventPath :=
  fun k => if hk : k < N then h ⟨k, hk⟩
    else if hN : 0 < N then
      let z := h ⟨N - 1, by omega⟩
      (z.1, (z.1.1, .inl ()))
    else (initialState N, (0, .inl ()))

theorem kingmanCompletion_prefix (N : ℕ) (h : KingmanHistory N)
    (k : ℕ) (hk : k < N) : kingmanCompletion N h k = h ⟨k, hk⟩ := by
  simp only [kingmanCompletion, dite_eq_left hk]

theorem KingmanHistorySupported.completion_init {N : ℕ} {h : KingmanHistory N}
    (hs : KingmanHistorySupported N h) :
    (kingmanCompletion N h 0).1 = initialState N := by
  by_cases hN : 0 < N
  · rw [kingmanCompletion_prefix N h 0 hN, hs.2.1 hN]
  · simp only [kingmanCompletion, dite_eq_right hN]

theorem KingmanHistorySupported.completion_step {N : ℕ} {h : KingmanHistory N}
    (hs : KingmanHistorySupported N h) (k : ℕ) :
    KingmanTransition (kingmanCompletion N h k, kingmanCompletion N h (k + 1)) := by
  by_cases hk : k + 1 < N
  · have hk0 : k < N := by omega
    rw [kingmanCompletion_prefix N h k hk0, kingmanCompletion_prefix N h (k + 1) hk]
    exact hs.2.2 ⟨k, by omega⟩
  · by_cases hN : 0 < N
    · have hf : (h ⟨N - 1, by omega⟩).1.2.2.1 = 1 := by
        have hc := (hs.1 ⟨N - 1, by omega⟩).2
        change (h ⟨N - 1, by omega⟩).1.2.2.1 = N - (N - 1) at hc
        omega
      have hnext : kingmanCompletion N h (k + 1) =
          ((h ⟨N - 1, by omega⟩).1, ((h ⟨N - 1, by omega⟩).1.1, .inl ())) := by
        simp only [kingmanCompletion, dite_eq_right hk, dite_eq_left hN]
      rw [hnext]
      by_cases hk0 : k < N
      · have heq : k = N - 1 := by omega
        subst k
        rw [kingmanCompletion_prefix N h (N - 1) (by omega)]
        simp only [KingmanTransition, hf, Nat.not_ofNat_le_one, ite_false, and_self]
      · have hprev : kingmanCompletion N h k =
            ((h ⟨N - 1, by omega⟩).1, ((h ⟨N - 1, by omega⟩).1.1, .inl ())) := by
          simp only [kingmanCompletion, dite_eq_right hk0, dite_eq_left hN]
        rw [hprev]
        simp only [KingmanTransition, hf, Nat.not_ofNat_le_one, ite_false, and_self]
    · have hk0 : ¬ k < N := by omega
      simp only [kingmanCompletion, dite_eq_right hk0, dite_eq_right hk, dite_eq_right hN]
      have hn : N = 0 := by omega
      subst N
      simp [KingmanTransition, initialState]

theorem KingmanHistorySupported.completion_valid {N : ℕ} {h : KingmanHistory N}
    (hs : KingmanHistorySupported N h) (k : ℕ) : Valid (kingmanCompletion N h k).1 := by
  by_cases hk : k < N
  · rw [kingmanCompletion_prefix N h k hk]
    exact (hs.1 ⟨k, hk⟩).1
  · by_cases hN : 0 < N
    · simpa only [kingmanCompletion, dite_eq_right hk, dite_eq_left hN] using
        (hs.1 ⟨N - 1, by omega⟩).1
    · simp only [kingmanCompletion, dite_eq_right hk, dite_eq_right hN]
      exact initialState_valid N

end Rhone.Coalescent.SmcPrime
