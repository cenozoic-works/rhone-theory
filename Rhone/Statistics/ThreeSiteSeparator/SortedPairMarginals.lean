/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SortedPairSupport
public import Rhone.Statistics.ThreeSiteSeparator.UnitSquareMarginals

/-! # Scalar moments of the sorted-iid pair law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma sortedPair_fst_CDF (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) {x : ℝ} (hx : x ≤ 1) :
    ((sortedPairLaw μ).map Prod.fst).real (Iic x) = (μ.real (Iic x))^3 := by
  rw [unitSquare_fst_CDF _ (sortedPairLaw_unit_support μ hμ), sortedPairLaw_CDF]
  unfold cdfJointFunction
  rw [min_eq_left hx]
  ring

lemma sortedPair_snd_CDF (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) {y : ℝ} (hy : y ≤ 1) :
    ((sortedPairLaw μ).map Prod.snd).real (Iic y) =
      (3*μ.real (Iic y)-(μ.real (Iic y))^3)/2 := by
  rw [unitSquare_snd_CDF _ (sortedPairLaw_unit_support μ hμ), sortedPairLaw_CDF]
  unfold cdfJointFunction
  rw [min_eq_right hy]
  dsimp only
  rw [unit_CDF_one μ hμ]
  ring

lemma sortedPair_fst_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (r : ℕ) :
    (∫ z, z.1^(r+1) ∂sortedPairLaw μ) =
      1-((r : ℝ)+1)*weightedPrimitive r (fun x => (μ.real (Iic x))^3) 1 := by
  let : IsProbabilityMeasure (sortedPairLaw μ) := sortedPairLaw_probability μ
  let : IsProbabilityMeasure ((sortedPairLaw μ).map Prod.fst) :=
    inferInstance
  have h := unit_moment_CDF ((sortedPairLaw μ).map Prod.fst)
    (unitSquare_fst_support _ (sortedPairLaw_unit_support μ hμ)) r
  rw [integral_map_of_stronglyMeasurable measurable_fst (by fun_prop)] at h
  rw [h]
  congr 2
  unfold weightedPrimitive
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  dsimp only
  rw [sortedPair_fst_CDF μ hμ hx.2]

lemma sortedPair_snd_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1)
    (hF : Continuous (fun x => μ.real (Iic x))) (r : ℕ) :
    (∫ z, z.2^(r+1) ∂sortedPairLaw μ) =
      1-(3*((r : ℝ)+1)/2)*weightedPrimitive r (fun x => μ.real (Iic x)) 1 +
        (((r : ℝ)+1)/2)*weightedPrimitive r (fun x => (μ.real (Iic x))^3) 1 := by
  let : IsProbabilityMeasure (sortedPairLaw μ) := sortedPairLaw_probability μ
  let : IsProbabilityMeasure ((sortedPairLaw μ).map Prod.snd) :=
    inferInstance
  have h := unit_moment_CDF ((sortedPairLaw μ).map Prod.snd)
    (unitSquare_snd_support _ (sortedPairLaw_unit_support μ hμ)) r
  rw [integral_map_of_stronglyMeasurable measurable_snd (by fun_prop)] at h
  have he : weightedPrimitive r (fun x => ((sortedPairLaw μ).map Prod.snd).real (Iic x)) 1 =
      (3/2 : ℝ)*weightedPrimitive r (fun x => μ.real (Iic x)) 1 -
        (1/2 : ℝ)*weightedPrimitive r (fun x => (μ.real (Iic x))^3) 1 := by
    have hi : (fun x => x^r*((3*μ.real (Iic x)-(μ.real (Iic x))^3)/2)) =
        fun x => (3/2 : ℝ)*(x^r*μ.real (Iic x))-(1/2 : ℝ)*(x^r*(μ.real (Iic x))^3) := by
      funext x
      ring
    unfold weightedPrimitive
    calc
      _ = ∫ x in (0 : ℝ)..1, x^r*((3*μ.real (Iic x)-(μ.real (Iic x))^3)/2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        dsimp only
        rw [sortedPair_snd_CDF μ hμ hx.2]
      _ = _ := by
        rw [hi, intervalIntegral.integral_sub
          ((show Continuous (fun x : ℝ => (3/2 : ℝ)*(x^r*μ.real (Iic x))) by
            fun_prop).intervalIntegrable _ _)
          ((show Continuous (fun x : ℝ => (1/2 : ℝ)*(x^r*(μ.real (Iic x))^3)) by
            fun_prop).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [h, he]
  ring

end Rhone.Statistics.ThreeSiteSeparator
