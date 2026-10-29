/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SourceScore

/-! # A whole positive-migration interval has a positive source score -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.ThreeSiteSeparator

def sourceNumerator (m : ℝ) : ℝ :=
  1209600-63109590*m-177529421*m^2-174191893*m^3-73478880*m^4-11287980*m^5

def sourceDenominator (m : ℝ) : ℝ :=
  (5*m+3)^2*(9*m+10)^2*(13*m+21)*(17*m+40)

lemma sourceScore_factor {m : ℝ} (hm : 0 ≤ m) :
    sourceScore m = 28*m*sourceNumerator m/sourceDenominator m := by
  have h15 : 15+14*m ≠ 0 := ne_of_gt (by positivity)
  have h35 : 35+22*m ≠ 0 := ne_of_gt (by positivity)
  have h63 : 63+30*m ≠ 0 := ne_of_gt (by positivity)
  have h80 : 80+34*m ≠ 0 := ne_of_gt (by positivity)
  have h6 : 6+10*m ≠ 0 := ne_of_gt (by positivity)
  have h20 : 20+18*m ≠ 0 := ne_of_gt (by positivity)
  have h42 : 42+26*m ≠ 0 := ne_of_gt (by positivity)
  have h3 : 5*m+3 ≠ 0 := ne_of_gt (by positivity)
  have h10 : 9*m+10 ≠ 0 := ne_of_gt (by positivity)
  have h21 : 13*m+21 ≠ 0 := ne_of_gt (by positivity)
  have h40 : 17*m+40 ≠ 0 := ne_of_gt (by positivity)
  norm_num [sourceScore, sourceMoment, score, linearScore, sourceNumerator, sourceDenominator]
  field_simp
  ring

lemma sourceNumerator_pos {m : ℝ} (hm : 0 ≤ m) (hsmall : m ≤ 1 / 1000) :
    0 < sourceNumerator m := by
  have h1 : m ≤ 1 := by linarith
  have h2 : m^2 ≤ m := by nlinarith
  have h3 : m^3 ≤ m := by
    calc
      m^3 = m^2*m := by ring
      _ ≤ m*m := mul_le_mul_of_nonneg_right h2 hm
      _ ≤ m := by nlinarith
  have h4 : m^4 ≤ m := by
    calc
      m^4 = m^3*m := by ring
      _ ≤ m*m := mul_le_mul_of_nonneg_right h3 hm
      _ ≤ m := by nlinarith
  have h5 : m^5 ≤ m := by
    calc
      m^5 = m^4*m := by ring
      _ ≤ m*m := mul_le_mul_of_nonneg_right h4 hm
      _ ≤ m := by nlinarith
  unfold sourceNumerator
  linarith

lemma sourceScore_small_positive {m : ℝ} (hm : 0 < m) (hsmall : m ≤ 1 / 1000) :
    0 < sourceScore m := by
  rw [sourceScore_factor hm.le]
  apply div_pos
  · exact mul_pos (mul_pos (by norm_num) hm) (sourceNumerator_pos hm.le hsmall)
  · unfold sourceDenominator
    positivity

end Rhone.Statistics.ThreeSiteSeparator
