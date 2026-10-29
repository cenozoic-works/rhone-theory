/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.KernelAlgebra
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The signed kernel has an explicitly nonpositive tail integral -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

def primitive (x t : ℝ) : ℝ :=
  (373275 / 2 : ℝ) * x^4 * t^2 - (926100 / 4 : ℝ) * x^2 * t^4 +
    (216405 / 6 : ℝ) * t^6

lemma primitive_deriv (x t : ℝ) : HasDerivAt (primitive x) (kernel x t) t := by
  have h2 := (hasDerivAt_pow 2 t).const_mul ((373275 / 2 : ℝ) * x^4)
  have h4 := (hasDerivAt_pow 4 t).const_mul ((926100 / 4 : ℝ) * x^2)
  have h6 := (hasDerivAt_pow 6 t).const_mul (216405 / 6 : ℝ)
  convert! (h2.sub h4).add h6 using 1
  simp only [kernel]
  ring

lemma primitive_sub (x t : ℝ) : primitive x x - primitive x t = tail x t := by
  unfold primitive tail
  ring

lemma kernel_continuous (x : ℝ) : Continuous (kernel x) := by
  unfold kernel
  fun_prop

lemma integral_kernel (x t : ℝ) : (∫ y in t..x, kernel x y) = tail x t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => primitive_deriv x y) ((kernel_continuous x).intervalIntegrable t x),
    primitive_sub]

lemma integral_kernel_nonpos {x t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) :
    (∫ y in t..x, kernel x y) ≤ 0 := by
  rw [integral_kernel]
  exact tail_nonpos ht htx

end Rhone.Statistics.ThreeSiteSeparator
