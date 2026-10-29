/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanFiniteSupport

/-! # Finite prefix extraction retains birth times and sample labels -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem ancestorLabel_eq_of_prefix (N : ℕ) (ω η : EventPath)
    (q : GenomicProbe) (i : Fin N) (k : ℕ)
    (h : ∀ l, l ≤ k → ω l = η l) :
    ancestorLabel N ω q i k = ancestorLabel N η q i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ancestorLabel, h k (by omega), h (k + 1) le_rfl,
      ih (fun l hl => h l (by omega))]

theorem pairBirthTime_eq_of_prefix (ω η : EventPath) (k a : ℕ)
    (h : ∀ l, l ≤ k → ω l = η l) : pairBirthTime ω k a = pairBirthTime η k a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pairBirthTime, h k (by omega), h (k + 1) le_rfl,
      ih (fun l hl => h l (by omega))]

theorem historyExtension_of_path (N : ℕ) (ω : EventPath) (k : ℕ) (hk : k < N) :
    historyExtension N (fun j : Fin N => ω j.val) k = ω k := by
  simp only [historyExtension, dite_eq_left hk]

end Rhone.Coalescent.SmcPrime
