/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.PanPairTransform

/-! # Equal-width histogram law and its exact clipped CDF -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Rhone.Statistics.BinnedPanLaw
open AtomicSmoothing

variable {n : ℕ}

def binCenter (n : ℕ) (i : Fin n) : ℝ := (i + 1 / 2) / n

def binWidth (n : ℕ) : ℝ := 1 / (2 * n)

def histogram (w : Fin n → ℝ) : Measure ℝ :=
  ∑ i : Fin n, ENNReal.ofReal (w i) • branchLaw (binCenter n i) (binWidth n) false

def histogramCDF (w : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, w i * clip (n * x - i)

instance histogram_finite (w : Fin n → ℝ) : IsFiniteMeasure (histogram w) := by
  unfold histogram
  infer_instance

theorem histogram_probability (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) : IsProbabilityMeasure (histogram w) := by
  constructor
  simp only [histogram, Measure.finsetSum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hs, ENNReal.ofReal_one]

theorem histogram_real_Iic (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (x : ℝ) :
    (histogram w).real (Iic x) = histogramCDF w x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [measureReal_def, histogram, Measure.finsetSum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hw i), branchLaw_false_Iic _ (by unfold binWidth; positivity)]
    have he : (x - (binCenter n i - binWidth n)) / (2 * binWidth n) = n * x - i := by
      unfold binCenter binWidth
      field_simp
      ring
    rw [he, ENNReal.toReal_ofReal (clip_nonnegative _)]
  · intro i _
    exact measure_ne_top _ _

theorem histogramCDF_lipschitz (w : Fin n → ℝ) : ∃ K, LipschitzWith K (histogramCDF w) := by
  apply exists_lipschitz_sum Finset.univ
  intro i _
  apply exists_lipschitz_scaled
  obtain ⟨K, hK⟩ := exists_lipschitz_scaled (n : ℝ) ⟨1, LipschitzWith.id⟩
  exact ⟨_, clip_lipschitz.comp (hK.sub (LipschitzWith.const (i : ℝ)))⟩

theorem histogramCDF_monotone (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Monotone (histogramCDF w) := by
  intro x y hxy
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply clip_monotone
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg n)) _

theorem histogramCDF_zero (w : Fin n → ℝ) : histogramCDF w 0 = 0 := by
  unfold histogramCDF
  have he (i : Fin n) : clip (-(i : ℝ)) = 0 :=
    clip_zero (neg_nonpos.mpr (Nat.cast_nonneg i.val))
  simp only [mul_zero, zero_sub, he, Finset.sum_const_zero]

theorem histogramCDF_one (w : Fin n → ℝ) (hs : ∑ i, w i = 1) :
    histogramCDF w 1 = 1 := by
  unfold histogramCDF
  have he (i : Fin n) : clip ((n : ℝ) - i) = 1 := by
    apply clip_one
    have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    linarith
  simp only [mul_one, he, hs]

theorem histogramCDF_positive (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    {x : ℝ} (hx : 0 < x) : 0 < histogramCDF w x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < clip ((n : ℝ) * x) :=
    (lt_min zero_lt_one (mul_pos hn' hx)).trans_le (le_max_right _ _)
  apply lt_of_lt_of_le (mul_pos (hw ⟨0, hn⟩) hp)
  have h := Finset.single_le_sum
    (f := fun i : Fin n => w i * clip (n * x - i))
    (fun i _ => mul_nonneg (hw i).le (clip_nonnegative _))
    (Finset.mem_univ (⟨0, hn⟩ : Fin n))
  simpa only [histogramCDF, Nat.cast_zero, sub_zero] using h

end Rhone.Statistics.BinnedPanLaw
