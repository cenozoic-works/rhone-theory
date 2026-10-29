/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.NoiseKernel

/-! # The exact CDF of the uniform noise and elementary clipping identities -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Rhone.Statistics.AtomicSmoothing

def clip (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clip_nonnegative (x : ℝ) : 0 ≤ clip x := le_max_left _ _
lemma clip_le_one (x : ℝ) : clip x ≤ 1 := max_le (by norm_num) (min_le_left _ _)

lemma clip_zero {x : ℝ} (hx : x ≤ 0) : clip x = 0 := by
  rw [clip, min_eq_right (hx.trans (by norm_num)), max_eq_left hx]

lemma clip_one {x : ℝ} (hx : 1 ≤ x) : clip x = 1 := by
  rw [clip, min_eq_left hx, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

lemma clip_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clip x = x := by
  rw [clip, min_eq_right h1, max_eq_right h0]

lemma clip_lipschitz : LipschitzWith 1 clip :=
  (LipschitzWith.id.const_min 1).const_max 0

lemma noiseMeasure_Iic (x : ℝ) :
    noiseMeasure (Iic x) = ENNReal.ofReal (clip ((x + 1) / 2)) := by
  have hi : Iic x ∩ Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) (min x 1) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [noiseMeasure, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, hi,
    Real.volume_Icc, smul_eq_mul, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  by_cases hx : x ≤ -1
  · have hx1 : x ≤ 1 := by linarith
    have hz : (x + 1) / 2 ≤ 0 := by linarith
    rw [min_eq_left hx1, clip_zero hz, ENNReal.ofReal_zero,
      ENNReal.ofReal_of_nonpos (by linarith)]
  · by_cases h1 : x ≤ 1
    · have h0 : 0 ≤ (x + 1) / 2 := by linarith
      have hu : (x + 1) / 2 ≤ 1 := by linarith
      rw [min_eq_left h1, clip_self h0 hu]
      congr 1
      ring
    · have hx1 : 1 ≤ x := le_of_not_ge h1
      have hu : 1 ≤ (x + 1) / 2 := by linarith
      rw [min_eq_right hx1, clip_one hu]
      norm_num

lemma noiseMeasure_real_Iic (x : ℝ) : noiseMeasure.real (Iic x) = clip ((x + 1) / 2) := by
  rw [measureReal_def, noiseMeasure_Iic, ENNReal.toReal_ofReal (clip_nonnegative _)]

end Rhone.Statistics.AtomicSmoothing
