/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.JointMomentCDF

/-! # Marginal CDFs of laws supported on the unit square -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma unitSquare_fst_support (ν : Measure (ℝ × ℝ))
    (hν : ∀ᵐ z ∂ν, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂ν.map Prod.fst, x ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff measurable_fst.aemeasurable (by measurability)).mpr
  exact hν.mono fun _ h => h.1

lemma unitSquare_snd_support (ν : Measure (ℝ × ℝ))
    (hν : ∀ᵐ z ∂ν, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂ν.map Prod.snd, x ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff measurable_snd.aemeasurable (by measurability)).mpr
  exact hν.mono fun _ h => h.2

lemma unitSquare_fst_CDF (ν : Measure (ℝ × ℝ))
    (hν : ∀ᵐ z ∂ν, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    (ν.map Prod.fst).real (Iic x) = rectangleCDF ν (x,1) := by
  rw [map_measureReal_apply measurable_fst measurableSet_Iic]
  apply measureReal_congr
  filter_upwards [hν] with z hz
  change (z.1 ≤ x) = (z.1 ≤ x ∧ z.2 ≤ 1)
  exact propext (and_iff_left hz.2.2).symm

lemma unitSquare_snd_CDF (ν : Measure (ℝ × ℝ))
    (hν : ∀ᵐ z ∂ν, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1) (y : ℝ) :
    (ν.map Prod.snd).real (Iic y) = rectangleCDF ν (1,y) := by
  rw [map_measureReal_apply measurable_snd measurableSet_Iic]
  apply measureReal_congr
  filter_upwards [hν] with z hz
  change (z.2 ≤ y) = (z.1 ≤ 1 ∧ z.2 ≤ y)
  exact propext (and_iff_right hz.1.2).symm

lemma unit_CDF_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) : μ.real (Iic 1) = 1 := by
  have he : Iic (1 : ℝ) =ᵐ[μ] univ := by
    filter_upwards [hμ] with z hz
    change (z ≤ 1) = True
    exact propext (iff_true_intro hz.2)
  rw [measureReal_congr he, probReal_univ]

end Rhone.Statistics.ThreeSiteSeparator
