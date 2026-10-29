/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.EncodingMoments

/-! # Monomial formula for the compact sorted-iid candidate family -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator DependentPairedTest

def realized (μ : ProbabilityMeasure CompactTime) : Measure ℝ :=
  (μ : Measure CompactTime).map Subtype.val

instance realized_probability (μ : ProbabilityMeasure CompactTime) :
    IsProbabilityMeasure (realized μ) :=
  by change IsProbabilityMeasure (Measure.map _ _); infer_instance

theorem realized_unit_support (μ : ProbabilityMeasure CompactTime) :
    ∀ᵐ x ∂realized μ, x ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  exact Filter.Eventually.of_forall fun x => x.property

theorem triple_lift_integral (μ : ProbabilityMeasure CompactTime) (f : RightCube → ℝ)
    (hf : Measurable f) :
    (∫ z, f z ∂(realized μ).prod ((realized μ).prod (realized μ))) =
      ∫ z : CompactTriple, f (z.1.val, z.2.1.val, z.2.2.val)
        ∂(μ : Measure CompactTime).prod ((μ : Measure CompactTime).prod μ) := by
  unfold realized
  rw [Measure.map_prod_map (μ : Measure CompactTime) μ
    (measurable_subtype_coe : Measurable (Subtype.val : CompactTime → ℝ))
      (measurable_subtype_coe : Measurable (Subtype.val : CompactTime → ℝ)),
    Measure.map_prod_map (μ : Measure CompactTime)
      ((μ : Measure CompactTime).prod (μ : Measure CompactTime))
      (measurable_subtype_coe : Measurable (Subtype.val : CompactTime → ℝ))
      ((measurable_subtype_coe : Measurable (Subtype.val : CompactTime → ℝ)).prodMap
        (measurable_subtype_coe : Measurable (Subtype.val : CompactTime → ℝ))),
    integral_map (measurable_subtype_coe.prodMap
      (measurable_subtype_coe.prodMap measurable_subtype_coe)).aemeasurable hf.aestronglyMeasurable]
  rfl

def pairMoment (μ : ProbabilityMeasure CompactTime) (p q : ℕ) : ℝ :=
  ∫ z, z.1 ^ p * z.2 ^ q ∂sortedPairLaw (realized μ)

theorem pair_moment_compact (μ : ProbabilityMeasure CompactTime) (p q : ℕ) :
    pairMoment μ p q =
      (1 / 2 : ℝ) * (∫ z : CompactTriple, (high z).val ^ p * (low z).val ^ q
        ∂(μ : Measure CompactTime).prod ((μ : Measure CompactTime).prod μ)) +
      (1 / 2 : ℝ) * (∫ z : CompactTriple, (high z).val ^ p * (middle z).val ^ q
        ∂(μ : Measure CompactTime).prod ((μ : Measure CompactTime).prod μ)) := by
  unfold pairMoment
  rw [sortedPairLaw_monomial_integral (realized μ) (realized_unit_support μ),
    triple_lift_integral μ _ (by fun_prop), triple_lift_integral μ _ (by fun_prop)]
  rfl

theorem select_encoding_monomial (n : Fin 3 → ℕ) (z : CompactTriple × Selection) :
    (∏ i, (selectEncoding z i).val ^ n i) =
      (high z.1).val ^ n z.2.2 *
        (if z.2.1 = 0 then (low z.1).val else (middle z.1).val) ^ otherPower n z.2.2 := by
  have hv (i : Fin 3) : (selectEncoding z i).val =
      if i = z.2.2 then (high z.1).val else
        if z.2.1 = 0 then (low z.1).val else (middle z.1).val := by
    unfold selectEncoding
    split
    · rfl
    · split <;> rfl
  simp only [hv]
  exact two_level_product n z.2.2 _ _

theorem compact_pan_monomial (μ : ProbabilityMeasure CompactTime) (n : Fin 3 → ℕ) :
    monoMoment n (compactPan μ) =
      ∑ q : Fin 3, (1 / 3 : ℝ) * pairMoment μ (n q) (otherPower n q) := by
  let f : (CompactTriple × Selection) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z => ∏ i, (selectEncoding z i).val ^ n i, by
      apply continuous_finsetProd
      intro i _
      exact ((continuous_subtype_val.comp
        ((continuous_apply i).comp select_encoding_continuous)).pow (n i))⟩
  change (∫ x : Cube 3, ∏ i, (x i).val ^ n i ∂Measure.map selectEncoding
    (((μ : Measure CompactTime).prod ((μ : Measure CompactTime).prod μ)).prod
      (lawMeasure selectionLaw))) = _
  have hm : Measurable (fun x : Cube 3 => ∏ i, (x i).val ^ n i) := by fun_prop
  rw [integral_map select_encoding_continuous.measurable.aemeasurable hm.aestronglyMeasurable]
  change (∫ x, f x ∂((μ : Measure CompactTime).prod
    ((μ : Measure CompactTime).prod μ)).prod (lawMeasure selectionLaw)) = _
  rw [integral_prod_symm _ (f.integrable _), integral_fintype Integrable.of_finite]
  dsimp only [f, BoundedContinuousFunction.mkOfCompact]
  simp only [law_measure_real_singleton, selectionLaw, smul_eq_mul]
  simp_rw [select_encoding_monomial]
  rw [Fintype.sum_prod_type]
  norm_num only [Fin.sum_univ_two]
  simp_rw [pair_moment_compact]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  change (1 / 6 : ℝ) * (∫ z : CompactTriple, (high z).val ^ n q *
    (low z).val ^ otherPower n q ∂(μ : Measure CompactTime).prod
      ((μ : Measure CompactTime).prod μ)) +
    (1 / 6 : ℝ) * (∫ z : CompactTriple, (high z).val ^ n q *
    (middle z).val ^ otherPower n q ∂(μ : Measure CompactTime).prod
      ((μ : Measure CompactTime).prod μ)) = _
  ring

end Rhone.Statistics.WeakRegularSeparation
