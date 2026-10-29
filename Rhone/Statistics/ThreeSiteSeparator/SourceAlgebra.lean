/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.Score

/-! # A rational positive source-score certificate -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.ThreeSiteSeparator

def sourceMoment (p q : ℕ) (m : ℝ) : ℝ :=
  let a : ℝ := p + q
  let den := (a+3)*(a+1)+(4*a+6)*m
  if q = 0 then 3*(a+1+2*m)/den else
    3*((a+1+m)*(q+2*m)+2*m^2)/(den*((q:ℝ)*(q+1)+2*(2*q+1)*m))

def sourceScore (m : ℝ) : ℝ :=
  score ((sourceMoment 2 0 m + 2*sourceMoment 0 2 m)/3)
    ((sourceMoment 4 0 m + 2*sourceMoment 0 4 m)/3)
    ((sourceMoment 6 0 m + 2*sourceMoment 0 6 m)/3)
    ((sourceMoment 5 2 m + 2*sourceMoment 1 6 m)/3)
    ((2*sourceMoment 3 4 m + sourceMoment 1 6 m)/3)

lemma sourceScore_one_hundredth :
    sourceScore (1/100) = (10464089628335504 / 53591027136025535 : ℝ) := by
  norm_num [sourceScore, sourceMoment, score, linearScore]

lemma sourceScore_one_hundredth_pos : 0 < sourceScore (1/100) := by
  rw [sourceScore_one_hundredth]
  norm_num

end Rhone.Statistics.ThreeSiteSeparator
