/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.KernelAlgebra

/-! # Explicit observable score and its negative-energy normalization -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.ThreeSiteSeparator

def linearScore (a p2 p3 h j : ℝ) : ℝ :=
  4977*h - 5145*j + 2058*p2 - 711*a - 1603*p3

def score (a p2 p3 h j : ℝ) : ℝ :=
  20 * linearScore a p2 p3 h j + 512 -
    52290*(a - 1 / 3)^2 - 48090*(a - 1 / 3)*(p3 - 1 / 7) + 77175*(p2 - 1 / 5)^2

def boundary (u v w : ℝ) : ℝ := 156870*u^2 + 432810*u*w - 926100*v^2

lemma score_normalization (a p2 p3 h j : ℝ) :
    score a p2 p3 h j = (4 / 3 : ℝ) *
      (15 * linearScore a p2 p3 h j + 384 -
        boundary (-(a - 1 / 3) / 2) (-(p2 - 1 / 5) / 4) (-(p3 - 1 / 7) / 6)) := by
  unfold score boundary
  ring

lemma score_nonpos_of_energy (a p2 p3 h j : ℝ)
    (he : 15 * linearScore a p2 p3 h j + 384 ≤
      boundary (-(a - 1 / 3) / 2) (-(p2 - 1 / 5) / 4) (-(p3 - 1 / 7) / 6)) :
    score a p2 p3 h j ≤ 0 := by
  rw [score_normalization]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr he)

end Rhone.Statistics.ThreeSiteSeparator
