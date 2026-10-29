/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.NoiseCDF

/-! # The one-dimensional probability components behind the noise kernels -/

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Rhone.Statistics.AtomicSmoothing

def branchLaw (a τ : ℝ) (b : Bool) : Measure ℝ := noiseMeasure.map (mixedCoordinate a τ b)

lemma mixedCoordinate_measurable (a τ : ℝ) (b : Bool) : Measurable (mixedCoordinate a τ b) := by
  cases b <;> unfold mixedCoordinate <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

instance branchLaw_probability (a τ : ℝ) (b : Bool) : IsProbabilityMeasure (branchLaw a τ b) := by
  unfold branchLaw
  infer_instance

instance scaledBranch_finite (a τ c : ℝ) (b : Bool) :
    IsFiniteMeasure (ENNReal.ofReal c • branchLaw a τ b) :=
  (branchLaw a τ b).smul_finite ENNReal.ofReal_ne_top

def componentLaw (a τ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - τ) • branchLaw a τ false + ENNReal.ofReal τ • branchLaw a τ true

instance componentLaw_finite (a τ : ℝ) : IsFiniteMeasure (componentLaw a τ) := by
  unfold componentLaw
  infer_instance

lemma componentLaw_probability (a : ℝ) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    IsProbabilityMeasure (componentLaw a τ) := by
  constructor
  simp only [componentLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr h1) h0]
  norm_num

lemma branchLaw_false_Iic (a : ℝ) {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    branchLaw a τ false (Iic x) = ENNReal.ofReal (clip ((x - (a - τ)) / (2 * τ))) := by
  rw [branchLaw, Measure.map_apply (mixedCoordinate_measurable a τ false) measurableSet_Iic]
  have he : mixedCoordinate a τ false ⁻¹' Iic x = Iic ((x-a)/τ) := by
    ext v
    simp only [mem_preimage, mem_Iic, mixedCoordinate, Bool.false_eq_true, ↓reduceIte]
    rw [le_div_iff₀ hτ]
    constructor <;> intro hv <;> nlinarith
  rw [he, noiseMeasure_Iic]
  congr 2
  field_simp
  ring

lemma branchLaw_true_Iic (a τ x : ℝ) :
    branchLaw a τ true (Iic x) = ENNReal.ofReal (clip x) := by
  rw [branchLaw, Measure.map_apply (mixedCoordinate_measurable a τ true) measurableSet_Iic]
  have he : mixedCoordinate a τ true ⁻¹' Iic x = Iic (2*x-1) := by
    ext v
    simp only [mem_preimage, mem_Iic, mixedCoordinate, ↓reduceIte]
    constructor <;> intro hv <;> linarith
  rw [he, noiseMeasure_Iic]
  congr 2
  ring

def componentCDF (a τ x : ℝ) : ℝ :=
  (1 - τ) * clip ((x - (a - τ)) / (2 * τ)) + τ * clip x

lemma componentLaw_real_Iic (a : ℝ) {τ : ℝ} (hτ : 0 < τ) (h1 : τ ≤ 1) (x : ℝ) :
    (componentLaw a τ).real (Iic x) = componentCDF a τ x := by
  rw [componentLaw, measureReal_add_apply, measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr h1), ENNReal.toReal_ofReal hτ.le]
  simp only [measureReal_def, branchLaw_false_Iic a hτ, branchLaw_true_Iic,
    ENNReal.toReal_ofReal (clip_nonnegative _)]
  rfl

end Rhone.Statistics.AtomicSmoothing
