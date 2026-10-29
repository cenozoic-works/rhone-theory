/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Exact algebraic sign certificate for the candidate three-site separator kernel -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.ThreeSiteSeparator

def kernel (x y : ℝ) : ℝ :=
  373275 * x^4 * y - 926100 * x^2 * y^3 + 216405 * y^5

def tail (x t : ℝ) : ℝ :=
  (373275 / 2 : ℝ) * x^4 * (x^2 - t^2) -
  (926100 / 4 : ℝ) * x^2 * (x^4 - t^4) +
  (216405 / 6 : ℝ) * (x^6 - t^6)

lemma tail_factor (x t : ℝ) :
    tail x t = -(315 / 2 : ℝ) * (x^2 - t^2) *
      (56 * x^4 + 1241 * x^2 * t^2 - 229 * t^4) := by
  unfold tail
  ring

lemma bracket_decomposition (x t : ℝ) :
    56 * x^4 + 1241 * x^2 * t^2 - 229 * t^4 =
      56 * x^4 + 1012 * x^2 * t^2 + 229 * t^2 * (x^2 - t^2) := by ring

lemma tail_nonpos {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) : tail x t ≤ 0 := by
  have hx : 0 ≤ x := ht.trans htx
  have hsq : 0 ≤ x^2 - t^2 := by nlinarith
  rw [tail_factor, bracket_decomposition]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hsq
  · positivity

lemma tail_self (x : ℝ) : tail x x = 0 := by simp [tail]

end Rhone.Statistics.ThreeSiteSeparator
