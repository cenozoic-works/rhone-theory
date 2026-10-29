/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SortedPairLaw

/-! # Support and moment interpretation of the sorted iid law -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma low_le_middle (a b c : ℝ) :
    min a (min b c) ≤ a+b+c-max a (max b c)-min a (min b c) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma sorted_coordinates_unit {a b c : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
    max a (max b c) ∈ Icc (0 : ℝ) 1 ∧ min a (min b c) ∈ Icc (0 : ℝ) 1 ∧
      a+b+c-max a (max b c)-min a (min b c) ∈ Icc (0 : ℝ) 1 := by
  have hhi : max a (max b c) ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.1.trans (le_max_left _ _), max_le ha.2 (max_le hb.2 hc.2)⟩
  have hlo : min a (min b c) ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min ha.1 (le_min hb.1 hc.1), (min_le_left _ _).trans ha.2⟩
  exact ⟨hhi, hlo, hlo.1.trans (low_le_middle a b c), (middle_le_high a b c).trans hhi.2⟩

lemma iid_cube_unit_support (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ p : RightCube ∂μ.prod (μ.prod μ),
      p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.1 ∈ Icc (0 : ℝ) 1 ∧ p.2.2 ∈ Icc (0 : ℝ) 1 := by
  have hs : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst.ae hμ).and (Measure.quasiMeasurePreserving_snd.ae hμ)
  exact (Measure.quasiMeasurePreserving_fst.ae hμ).and (Measure.quasiMeasurePreserving_snd.ae hs)

lemma sortedLowerPair_unit_support (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂(μ.prod (μ.prod μ)).map sortedLowerPair,
      z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff sortedLowerPair_measurable.aemeasurable (by measurability)).mpr
  filter_upwards [iid_cube_unit_support μ hμ] with p hp
  have h := sorted_coordinates_unit hp.1 hp.2.1 hp.2.2
  exact ⟨h.1, h.2.1⟩

lemma sortedMiddlePair_unit_support (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂(μ.prod (μ.prod μ)).map sortedMiddlePair,
      z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff sortedMiddlePair_measurable.aemeasurable (by measurability)).mpr
  filter_upwards [iid_cube_unit_support μ hμ] with p hp
  have h := sorted_coordinates_unit hp.1 hp.2.1 hp.2.2
  exact ⟨h.1, h.2.2⟩

lemma sortedPairLaw_unit_support (μ : Measure ℝ) [SFinite μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂sortedPairLaw μ, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1 := by
  exact ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure (sortedLowerPair_unit_support μ hμ) (1/2 : NNReal),
      Measure.ae_smul_measure (sortedMiddlePair_unit_support μ hμ) (1/2 : NNReal)⟩

lemma sortedPairLaw_monomial_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (r s : ℕ) :
    (∫ z, z.1^r*z.2^s ∂sortedPairLaw μ) =
      (1/2 : ℝ)*(∫ p, (sortedLowerPair p).1^r*(sortedLowerPair p).2^s ∂μ.prod (μ.prod μ)) +
        (1/2 : ℝ)*(∫ p, (sortedMiddlePair p).1^r*(sortedMiddlePair p).2^s ∂μ.prod (μ.prod μ)) := by
  have hA := unitSquare_power_integrable _ (sortedLowerPair_unit_support μ hμ) r s
  have hB := unitSquare_power_integrable _ (sortedMiddlePair_unit_support μ hμ) r s
  unfold sortedPairLaw
  rw [integral_add_measure hA.smul_measure_nnreal hB.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_map_of_stronglyMeasurable sortedLowerPair_measurable (by fun_prop),
    integral_map_of_stronglyMeasurable sortedMiddlePair_measurable (by fun_prop)]
  norm_num [NNReal.smul_def, smul_eq_mul]

end Rhone.Statistics.ThreeSiteSeparator
