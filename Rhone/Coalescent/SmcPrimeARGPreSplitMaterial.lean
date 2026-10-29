/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGCoordinateWeights
public import Rhone.Coalescent.SmcSupport.StateSupport

/-! # Material and hull of flat ARG runs before and at the first split -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport

theorem argCoalNat_zeroSplit {s : State} (hs : ZeroSplitReachable s) (ij : ℕ × ℕ) :
    ZeroSplitReachable (coalSuccessorNat s ij) := by
  by_cases hi : ij.1 < s.2.2.1
  · by_cases hj : ij.2 < s.2.2.1
    · rw [coalSuccessorNat, dite_eq_left hi, dite_eq_left hj]
      exact ZeroSplitReachable.coal hs _ _
    · rw [coalSuccessorNat, dite_eq_left hi, dite_eq_right hj]
      exact hs
  · rw [coalSuccessorNat, dite_eq_right hi]
    exact hs

theorem argFlatRun_preSplit_zeroSplit (N : ℕ) {n : ℕ} (w : Fin n → Action)
    (τ : Fin n → ℝ) (x : ℝ) (s : Fin n)
    (hw : ∀ j : Fin n, j.val < s.val → ∃ ij, w j = .inl ij)
    (k : ℕ) (hk : k ≤ s.val) :
    ZeroSplitReachable (argFlatRun (initialState N, (0, .inl ())) w τ x k).1 := by
  induction k with
  | zero => exact ZeroSplitReachable.initial N
  | succ k ih =>
    have hkn : k < n := by have := s.isLt; omega
    obtain ⟨ij, hij⟩ := hw ⟨k, hkn⟩ (by change k < s.val; omega)
    rw [argFlatRun, dite_eq_left hkn, hij]
    exact ZeroSplitReachable.clock (argCoalNat_zeroSplit (ih (by omega)) ij) _

theorem argFlatRun_split_hull (N : ℕ) {n : ℕ} (w : Fin n → Action)
    (τ : Fin n → ℝ) (x : ℝ) (s : Fin n)
    (hw : ∀ j : Fin n, j ≠ s → ∃ ij, w j = .inl ij) (i : ℕ)
    (hi : i < (argFlatRun (initialState N, (0, .inl ())) w τ x s.val).1.2.2.1) :
    lineageHullEndpoint false (argFlatRun (initialState N, (0, .inl ())) w τ x s.val).1 i = 0 ∧
    lineageHullEndpoint true (argFlatRun (initialState N, (0, .inl ())) w τ x s.val).1 i = 1 := by
  have hs := argFlatRun_preSplit_zeroSplit N w τ x s
    (fun j hj => hw j (by intro he; have := congrArg Fin.val he; omega)) s.val le_rfl
  obtain ⟨hlo, hhi⟩ := constant_atoms_hull _ 0 1 (by norm_num)
    (zeroSplit_full hs ⟨i, hi⟩)
  simp only [lineageHullEndpoint, dite_eq_left hi, Bool.false_eq_true, ite_false, ite_true,
    hlo, hhi, and_self]
end Rhone.Coalescent.SmcPrime
