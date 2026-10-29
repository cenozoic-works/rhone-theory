/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.CompactPan

/-! # First-merger marginal and injectivity of the compact candidate family -/

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator DependentPairedTest

def maxEncoding (x : Cube 3) : ℝ := max (x 0).val (max (x 1).val (x 2).val)

theorem max_encoding_continuous : Continuous maxEncoding := by
  unfold maxEncoding
  fun_prop

theorem max_select_encoding (z : CompactTriple × Selection) :
    maxEncoding (selectEncoding z) = (high z.1).val := by
  rcases z with ⟨t, b, c⟩
  have hl : (low t).val ≤ (high t).val :=
    (min_le_left _ _).trans (le_max_left _ _)
  have hm : (middle t).val ≤ (high t).val := middle_le_high _ _ _
  fin_cases b <;> fin_cases c <;>
    simp [maxEncoding, selectEncoding, max_eq_left hl, max_eq_right hl,
      max_eq_left hm, max_eq_right hm]

theorem compact_pan_max_law (μ : ProbabilityMeasure CompactTime) :
    ((compactPan μ : Measure (Cube 3)).map maxEncoding) =
      ((μ : Measure CompactTime).prod ((μ : Measure CompactTime).prod μ)).map
        (fun z : CompactTriple => (high z).val) := by
  change Measure.map maxEncoding (Measure.map selectEncoding
    (((μ : Measure CompactTime).prod ((μ : Measure CompactTime).prod μ)).prod
      (lawMeasure selectionLaw))) = _
  rw [Measure.map_map max_encoding_continuous.measurable select_encoding_continuous.measurable]
  have he : maxEncoding ∘ selectEncoding =
      (fun z : CompactTriple × Selection => (high z.1).val) := funext max_select_encoding
  rw [he]
  have hh : Measurable (fun z : CompactTriple => (high z).val) :=
    (continuous_subtype_val.comp high_continuous).measurable
  change Measure.map ((fun z : CompactTriple => (high z).val) ∘ Prod.fst) _ = _
  rw [← Measure.map_map hh measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

theorem compact_pan_max_cdf (μ : ProbabilityMeasure CompactTime) (t : ℝ) :
    (((compactPan μ : Measure (Cube 3)).map maxEncoding).real (Iic t)) =
      (μ : Measure CompactTime).real {x | x.val ≤ t} ^ 3 := by
  have hh : Measurable (fun z : CompactTriple => (high z).val) :=
    (continuous_subtype_val.comp high_continuous).measurable
  rw [compact_pan_max_law, map_measureReal_apply hh measurableSet_Iic]
  have he : (fun z : CompactTriple => (high z).val) ⁻¹' Iic t =
      {x : CompactTime | x.val ≤ t} ×ˢ
        ({x : CompactTime | x.val ≤ t} ×ˢ {x : CompactTime | x.val ≤ t}) := by
    ext z
    simp [high]
  rw [he]
  simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  ring

theorem compact_pan_max_injective :
    Function.Injective (fun μ => (compactPan μ : Measure (Cube 3)).map maxEncoding) := by
  intro μ ν he
  dsimp only at he
  have hmax (t : ℝ) : (μ : Measure CompactTime).real {x | x.val ≤ t} =
      (ν : Measure CompactTime).real {x | x.val ≤ t} := by
    apply (show Odd 3 by decide).pow_injective
    dsimp only
    rw [← compact_pan_max_cdf μ t, ← compact_pan_max_cdf ν t, he]
  have hm : (μ : Measure CompactTime).map Subtype.val =
      (ν : Measure CompactTime).map Subtype.val := by
    apply Measure.ext_of_Iic
    intro t
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change ((μ : Measure CompactTime).map Subtype.val).real (Iic t) =
      ((ν : Measure CompactTime).map Subtype.val).real (Iic t)
    rw [map_measureReal_apply measurable_subtype_coe measurableSet_Iic,
      map_measureReal_apply measurable_subtype_coe measurableSet_Iic]
    exact hmax t
  apply ProbabilityMeasure.toMeasure_injective
  exact (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective hm

theorem compact_pan_injective : Function.Injective compactPan := by
  intro μ ν he
  apply compact_pan_max_injective
  dsimp only
  rw [he]

end Rhone.Statistics.WeakRegularSeparation
