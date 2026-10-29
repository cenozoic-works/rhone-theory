/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanBirth

/-! # Chronological Kingman records have strictly increasing pre-root clocks -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem KingmanTransition.time_le {p : AugmentedState × AugmentedState}
    (hp : KingmanTransition p) : p.1.1.1 ≤ p.2.1.1 := by
  by_cases hm : 2 ≤ p.1.1.2.2.1
  · obtain ⟨_, _, _, _, _, ht⟩ := (ite_eq_left hm).mp hp
    exact ht.le
  · obtain ⟨he, _⟩ := (ite_eq_right hm).mp hp
    change p.2.1 = p.1.1 at he
    rw [he]

theorem kingman_path_time_strict_next (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) (hk : k + 1 < N) :
    (ω k).1.1 < (ω (k + 1)).1.1 := by
  have hc := kingman_path_count N ω hinit hstep k (by omega)
  have hm : 2 ≤ (ω k).1.2.2.1 := by omega
  obtain ⟨_, _, _, _, _, ht⟩ := (ite_eq_left hm).mp (hstep k)
  exact ht

theorem kingman_path_time_strict (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k l : ℕ)
    (hkl : k < l) (hlN : l < N) : (ω k).1.1 < (ω l).1.1 := by
  induction l with
  | zero => omega
  | succ l ih =>
    have ht := kingman_path_time_strict_next N ω hinit hstep l hlN
    by_cases he : k = l
    · subst k
      exact ht
    · exact lt_trans (ih (by omega) (by omega)) ht

end Rhone.Coalescent.SmcPrime
