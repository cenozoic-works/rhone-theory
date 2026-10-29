/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Stationary
public import Rhone.MarkovChain.StationaryLaw
public import Mathlib.Basic.Real.Basic

/-! # Executable stationarity test equals the specification -/

@[expose] public section
namespace Rhone.Computation.Stationary
open MarkovChain Finset Matrix

theorem sumBy_range (g : Nat → Rat) (N : Nat) :
    sumBy g (List.range N) = ∑ i ∈ Finset.range N, g i := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, Finset.sum_range_succ, ← ih]
    clear ih
    generalize List.range N = l
    induction l with
    | nil => simp [sumBy]
    | cons x xs ih => simp [sumBy, ih, add_assoc]

theorem isStationary_iff {N : Nat} (R : RateChain (Fin N)) (Q : List (List Rat))
    (π : List Rat) (hN : π.length = N)
    (hQ : ∀ x y : Fin N, ((entry Q x y : Rat) : ℝ) = R.Q x y) :
    isStationary Q π = true ↔ R.IsStationary (fun x : Fin N => ((comp π x : Rat) : ℝ)) := by
  subst hN
  have hnn : (∀ x ∈ List.range π.length, 0 ≤ comp π x) ↔
      ∀ x : Fin π.length, 0 ≤ ((comp π x : Rat) : ℝ) := by
    constructor
    · intro h x
      exact_mod_cast h x (List.mem_range.2 x.2)
    · intro h x hx
      exact_mod_cast h ⟨x, List.mem_range.1 hx⟩
  have hsum : total π = 1 ↔ ∑ x : Fin π.length, ((comp π x : Rat) : ℝ) = 1 := by
    rw [total, sumBy_range, Fin.sum_univ_eq_sum_range (fun i => ((comp π i : Rat) : ℝ)),
      ← Rat.cast_sum]
    exact_mod_cast Iff.rfl
  have hcol : (∀ y ∈ List.range π.length, vecMulColumn Q π y = 0) ↔
      (fun x : Fin π.length => ((comp π x : Rat) : ℝ)) ᵥ* R.Q = 0 := by
    have key : ∀ y : Fin π.length, (((vecMulColumn Q π y : Rat)) : ℝ) =
        ((fun x : Fin π.length => ((comp π x : Rat) : ℝ)) ᵥ* R.Q) y := by
      intro y
      simp only [vecMulColumn, sumBy_range, Matrix.vecMul, dotProduct, Rat.cast_sum,
        Rat.cast_mul]
      rw [← Fin.sum_univ_eq_sum_range (fun i => ((comp π i : Rat) : ℝ) * ((entry Q i y : Rat) : ℝ))]
      exact Finset.sum_congr rfl fun x _ => by rw [hQ]
    constructor
    · intro h
      funext y
      rw [← key y]
      have := h y (List.mem_range.2 y.2)
      simp [this]
    · intro h y hy
      have := key ⟨y, List.mem_range.1 hy⟩
      rw [h, Pi.zero_apply] at this
      exact_mod_cast this
  unfold isStationary
  rw [decide_eq_true_iff, hnn, hsum, hcol]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

example : isStationary [[-1, 1], [2, -2]] [2 / 3, 1 / 3] = true ∧
    isStationary [[-1, 1], [2, -2]] [1 / 2, 1 / 2] = false := by
  constructor <;>
    (simp [isStationary, total, vecMulColumn, comp, entry, List.range_succ, sumBy]; norm_num)

end Rhone.Computation.Stationary
