/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SortedCDFIntegral
public import Rhone.Statistics.ThreeSiteSeparator.JointMomentCDF
public import Rhone.Statistics.ThreeSiteSeparator.CDFJointFunction

/-! # A probability-law realization of the symmetric three-iid genealogy kernel -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

abbrev RightCube := ℝ × ℝ × ℝ

def sortedLowerPair (p : RightCube) : ℝ × ℝ :=
  (max p.1 (max p.2.1 p.2.2), min p.1 (min p.2.1 p.2.2))

def sortedMiddlePair (p : RightCube) : ℝ × ℝ :=
  (max p.1 (max p.2.1 p.2.2), p.1+p.2.1+p.2.2 -
    max p.1 (max p.2.1 p.2.2)-min p.1 (min p.2.1 p.2.2))

@[fun_prop]
lemma sortedLowerPair_measurable : Measurable sortedLowerPair := by
  unfold sortedLowerPair
  fun_prop

@[fun_prop]
lemma sortedMiddlePair_measurable : Measurable sortedMiddlePair := by
  unfold sortedMiddlePair
  fun_prop

def sortedPairLaw (μ : Measure ℝ) : Measure (ℝ × ℝ) :=
  (1/2 : NNReal) • (μ.prod (μ.prod μ)).map sortedLowerPair +
    (1/2 : NNReal) • (μ.prod (μ.prod μ)).map sortedMiddlePair

instance sortedPairLaw_finite (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (sortedPairLaw μ) := by unfold sortedPairLaw; infer_instance

lemma sortedPairLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (sortedPairLaw μ) := by
  let : IsProbabilityMeasure ((μ.prod (μ.prod μ)).map sortedLowerPair) :=
    inferInstance
  let : IsProbabilityMeasure ((μ.prod (μ.prod μ)).map sortedMiddlePair) :=
    inferInstance
  constructor
  norm_num [sortedPairLaw, Measure.add_apply, Measure.smul_apply]
  exact ENNReal.inv_two_add_inv_two

lemma sortedPairLaw_CDF_integral (μ : Measure ℝ) [IsFiniteMeasure μ] (x y : ℝ) :
    rectangleCDF (sortedPairLaw μ) (x,y) =
      ∫ p : RightCube, sortedCDF x y p.1 p.2.1 p.2.2 ∂μ.prod (μ.prod μ) := by
  let A := sortedLowerPair ⁻¹' (Iic x ×ˢ Iic y)
  let B := sortedMiddlePair ⁻¹' (Iic x ×ˢ Iic y)
  have hA : MeasurableSet A :=
    sortedLowerPair_measurable (measurableSet_Iic.prod measurableSet_Iic)
  have hB : MeasurableSet B :=
    sortedMiddlePair_measurable (measurableSet_Iic.prod measurableSet_Iic)
  have hiA : Integrable (A.indicator (fun _ : RightCube => (1 : ℝ))) (μ.prod (μ.prod μ)) :=
    (integrable_const 1).indicator hA
  have hiB : Integrable (B.indicator (fun _ : RightCube => (1 : ℝ))) (μ.prod (μ.prod μ)) :=
    (integrable_const 1).indicator hB
  have he : (fun p : RightCube => sortedCDF x y p.1 p.2.1 p.2.2) =
      fun p => (A.indicator (fun _ => (1 : ℝ)) p+B.indicator (fun _ => (1 : ℝ)) p)/2 := by
    funext p
    simp [sortedCDF, A, B, Set.indicator, sortedLowerPair, sortedMiddlePair]
  rw [he, integral_div, integral_add hiA hiB, integral_indicator hA, integral_indicator hB]
  unfold rectangleCDF sortedPairLaw
  rw [measureReal_add_apply]
  simp only [measureReal_nnreal_smul_apply, NNReal.coe_div, NNReal.coe_one,
    map_measureReal_apply sortedLowerPair_measurable (measurableSet_Iic.prod measurableSet_Iic),
    map_measureReal_apply sortedMiddlePair_measurable (measurableSet_Iic.prod measurableSet_Iic),
    setIntegral_const, smul_eq_mul, mul_one]
  change (1/2 : ℝ)*(μ.prod (μ.prod μ)).real A +
    (1/2 : ℝ)*(μ.prod (μ.prod μ)).real B =
      ((μ.prod (μ.prod μ)).real A+(μ.prod (μ.prod μ)).real B)/2
  ring

theorem sortedPairLaw_CDF (μ : Measure ℝ) [IsFiniteMeasure μ] (x y : ℝ) :
    rectangleCDF (sortedPairLaw μ) (x,y) = cdfJointFunction (fun z => μ.real (Iic z)) x y := by
  rw [sortedPairLaw_CDF_integral]
  rcases le_total y x with hyx | hxy
  · rw [sortedCDF_iid_below μ hyx, cdfJointFunction, min_eq_right hyx]
  · rw [sortedCDF_iid_above μ hxy, cdfJointFunction, min_eq_left hxy]
    ring

end Rhone.Statistics.ThreeSiteSeparator
