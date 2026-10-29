/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.ComponentLaw

/-! # Positive finite mixtures of the noisy probability components -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace Rhone.Statistics.AtomicSmoothing

variable {α : Type*} [Fintype α]

def mixtureLaw (loc w : α → ℝ) (τ : ℝ) : Measure ℝ :=
  ∑ a : α, ENNReal.ofReal (w a) • componentLaw (loc a) τ

def mixtureCDF (loc w : α → ℝ) (τ x : ℝ) : ℝ :=
  ∑ a : α, w a * componentCDF (loc a) τ x

instance scaledComponent_finite (a τ c : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal c • componentLaw a τ) :=
  (componentLaw a τ).smul_finite ENNReal.ofReal_ne_top

instance mixtureLaw_finite (loc w : α → ℝ) (τ : ℝ) : IsFiniteMeasure (mixtureLaw loc w τ) := by
  unfold mixtureLaw
  infer_instance

lemma mixtureLaw_probability (loc w : α → ℝ) {τ : ℝ}
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) :
    IsProbabilityMeasure (mixtureLaw loc w τ) := by
  constructor
  rw [mixtureLaw, Measure.finsetSum_apply]
  have he (a : α) : (ENNReal.ofReal (w a) • componentLaw (loc a) τ) univ =
      ENNReal.ofReal (w a) := by
    let : IsProbabilityMeasure (componentLaw (loc a) τ) := componentLaw_probability _ h0 h1
    simp
  simp_rw [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hw a), hs, ENNReal.ofReal_one]

lemma mixtureLaw_real_Iic (loc w : α → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (h1 : τ ≤ 1) (hw : ∀ a, 0 ≤ w a) (x : ℝ) :
    (mixtureLaw loc w τ).real (Iic x) = mixtureCDF loc w τ x := by
  rw [measureReal_def, mixtureLaw, Measure.finsetSum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw a)]
    change w a * (componentLaw (loc a) τ).real (Iic x) = _
    rw [componentLaw_real_Iic _ hτ h1]
  · intro a _
    exact measure_ne_top _ _

lemma componentCDF_nonnegative (a x : ℝ) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    0 ≤ componentCDF a τ x := by
  unfold componentCDF
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr h1) (clip_nonnegative _))
    (mul_nonneg h0 (clip_nonnegative _))

lemma componentCDF_le_one (a x : ℝ) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    componentCDF a τ x ≤ 1 := by
  have hb := mul_le_mul_of_nonneg_left (clip_le_one ((x - (a - τ)) / (2 * τ)))
    (sub_nonneg.mpr h1)
  have hu := mul_le_mul_of_nonneg_left (clip_le_one x) h0
  unfold componentCDF
  nlinarith

lemma componentCDF_zero {a τ : ℝ} (hτ : 0 < τ) (hl : 0 ≤ a - τ) :
    componentCDF a τ 0 = 0 := by
  have he : (0 - (a - τ)) / (2 * τ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith) (by positivity)
  unfold componentCDF
  rw [clip_zero he, clip_zero le_rfl]
  ring

lemma componentCDF_one {a τ : ℝ} (hτ : 0 < τ) (hu : a + τ ≤ 1) :
    componentCDF a τ 1 = 1 := by
  have he : 1 ≤ (1 - (a - τ)) / (2 * τ) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * τ)).mpr (by linarith)
  simp [componentCDF, clip_one he, clip_one le_rfl]

lemma mixtureCDF_zero (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hl : ∀ a, 0 ≤ loc a - τ) : mixtureCDF loc w τ 0 = 0 := by
  simp [mixtureCDF, componentCDF_zero hτ (hl _)]

lemma mixtureCDF_one (loc w : α → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hu : ∀ a, loc a + τ ≤ 1) (hs : ∑ a, w a = 1) : mixtureCDF loc w τ 1 = 1 := by
  simp [mixtureCDF, componentCDF_one hτ (hu _), hs]

lemma mixtureCDF_lower (loc w : α → ℝ) {τ x : ℝ} (h1 : τ ≤ 1)
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    τ * x ≤ mixtureCDF loc w τ x := by
  have he : (∑ a : α, w a * (τ * x)) = τ * x := by rw [← Finset.sum_mul, hs, one_mul]
  rw [← he]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hw a)
  unfold componentCDF
  rw [clip_self hx0 hx1]
  exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr h1) (clip_nonnegative _))

end Rhone.Statistics.AtomicSmoothing
