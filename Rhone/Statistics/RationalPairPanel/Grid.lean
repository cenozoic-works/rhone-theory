/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic
public import Lean.Elab.Tactic.Omega

/-! # The finite rational-grid algebra -/

@[expose] public section

open Polynomial
namespace Rhone.Statistics.RationalPairPanel

theorem clock_grid_injective {n : ℕ} {k : ℝ} (hk : k ≠ 0) :
    Function.Injective (fun i : Fin n => (i : ℝ) * k) := by
  intro i j h
  have hh : (i : ℝ) = (j : ℝ) := mul_right_cancel₀ hk h
  exact Fin.ext (Nat.cast_injective hh)

theorem rational_grid_identity (P Q R T : ℝ[X]) {d e : ℕ} {k : ℝ}
    (hk : k ≠ 0) (hP : P.natDegree < d) (hQ : Q.natDegree ≤ d)
    (hR : R.natDegree < e) (hT : T.natDegree ≤ e)
    (hQn : ∀ i : Fin (d + e), Q.eval ((i : ℝ)*k) ≠ 0)
    (hTn : ∀ i : Fin (d + e), T.eval ((i : ℝ)*k) ≠ 0)
    (hgrid : ∀ i : Fin (d + e), P.eval ((i : ℝ)*k) / Q.eval ((i : ℝ)*k) =
      R.eval ((i : ℝ)*k) / T.eval ((i : ℝ)*k)) : P * T = R * Q := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (P * T-R * Q) (clock_grid_injective hk)
  · intro i
    simp only [eval_sub, eval_mul]
    exact sub_eq_zero.mpr ((div_eq_div_iff (hQn i) (hTn i)).mp (hgrid i))
  · simp only [Fintype.card_fin]
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt natDegree_mul_le (by omega)
    · exact lt_of_le_of_lt natDegree_mul_le (by omega)

theorem rational_eval_eq_of_identity {P Q R T : ℝ[X]} (h : P * T = R * Q)
    {s : ℝ} (hQ : Q.eval s ≠ 0) (hT : T.eval s ≠ 0) :
    P.eval s / Q.eval s = R.eval s / T.eval s := by
  apply (div_eq_div_iff hQ hT).mpr
  simpa using congrArg (fun p : ℝ[X] => p.eval s) h

theorem common_denominator_grid (P R Q : ℝ[X]) {d : ℕ} {k : ℝ}
    (hk : k ≠ 0) (hP : P.natDegree < d) (hR : R.natDegree < d)
    (hQ : ∀ i : Fin d, Q.eval ((i : ℝ)*k) ≠ 0)
    (hgrid : ∀ i : Fin d, P.eval ((i : ℝ)*k) / Q.eval ((i : ℝ)*k) =
      R.eval ((i : ℝ)*k) / Q.eval ((i : ℝ)*k)) : P = R := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P R (clock_grid_injective hk)
  · intro i
    exact (div_left_inj' (hQ i)).mp (hgrid i)
  · simpa only [Fintype.card_fin] using max_lt hP hR

end Rhone.Statistics.RationalPairPanel
