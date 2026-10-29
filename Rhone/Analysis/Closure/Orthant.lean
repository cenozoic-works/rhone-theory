/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Order.Interval.Set.Infinite

/-! # A nonzero polynomial does not vanish identically on the positive orthant -/

@[expose] public section

namespace Rhone.Analysis.Closure

open MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem eq_zero_of_eval_pos_eq_zero {p : MvPolynomial σ R}
    (h : ∀ x : σ → R, (∀ i, 0 < x i) → eval x p = 0) : p = 0 := by
  refine MvPolynomial.funext_set (p := p) (q := 0) (fun _ => Set.Ioi (0 : R))
    (fun _ => Set.Ioi_infinite 0) ?_
  intro x hx
  rw [map_zero]
  exact h x fun i => hx i (Set.mem_univ i)

theorem exists_pos_eval_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ x : σ → R, (∀ i, 0 < x i) ∧ eval x p ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hp (eq_zero_of_eval_pos_eq_zero fun x hx => hc x hx)

theorem exists_pos_eval₂_ne_zero {R S : Type*} [CommRing R] [CommRing S]
    [LinearOrder S] [IsStrictOrderedRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    {p : MvPolynomial σ R} (hp : p ≠ 0) :
    ∃ x : σ → S, (∀ i, 0 < x i) ∧ eval₂ φ x p ≠ 0 := by
  have hmap : MvPolynomial.map φ p ≠ 0 := fun h =>
    hp (MvPolynomial.map_injective φ hφ (by rw [h, map_zero]))
  obtain ⟨x, hx, hne⟩ := exists_pos_eval_ne_zero hmap
  exact ⟨x, hx, by rwa [MvPolynomial.eval_map] at hne⟩

end Rhone.Analysis.Closure
