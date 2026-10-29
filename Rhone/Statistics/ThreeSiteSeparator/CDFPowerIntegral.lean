/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SortedCDFIntegral
public import Rhone.Statistics.ThreeSiteSeparator.WeightedPrimitive

/-! # Layer-cake identity for moments of any probability law on the unit interval -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

lemma cutoff_power_integral (r : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (∫ x in Icc (0 : ℝ) 1, x^r*below x z) = (1 - z^(r + 1))/((r : ℝ) + 1) := by
  have he : (fun x : ℝ => x^r*below x z) = (Ici z).indicator (fun x => x^r) := by
    funext x
    simp only [below, indicator_apply, mem_Ici]
    split_ifs <;> simp
  rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hs : Ici z ∩ Icc (0 : ℝ) 1 = Icc z 1 := by
    ext x
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hz.1.trans h.1, h.2⟩
  rw [hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz.2, integral_pow]
  simp only [one_pow]

lemma unit_power_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (r : ℕ) :
    Integrable (fun z => z^r) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [hμ] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz.1 r)]
  exact pow_le_one₀ hz.1 hz.2

lemma cutoff_power_joint_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1^r*below p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod μ) := by
  have hm : Measurable (fun p : ℝ × ℝ => p.1^r*below p.1 p.2) := by
    unfold below
    exact (measurable_fst.pow_const r).mul
      (measurable_const.ite (measurableSet_le measurable_snd measurable_fst) measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  have hs : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1), x ∈ Icc 0 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs] with p hp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hp.1 r)]
  exact (mul_le_mul (pow_le_one₀ hp.1 hp.2) (below_abs_le_one _ _)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)

lemma weightedCDF_eq_power_tail (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (r : ℕ) :
    weightedPrimitive r (fun x => μ.real (Iic x)) 1 =
      ∫ z, (1 - z^(r + 1))/((r : ℝ) + 1) ∂μ := by
  unfold weightedPrimitive
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  simp_rw [← integral_below μ, ← integral_const_mul]
  rw [integral_integral_swap (cutoff_power_joint_integrable μ r)]
  apply integral_congr_ae
  filter_upwards [hμ] with z hz
  exact cutoff_power_integral r hz

theorem unit_moment_CDF (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (r : ℕ) :
    (∫ z, z^(r + 1) ∂μ) = 1 - ((r : ℝ) + 1)*weightedPrimitive r (fun x => μ.real (Iic x)) 1 := by
  rw [weightedCDF_eq_power_tail μ hμ, integral_div,
    integral_sub (integrable_const 1) (unit_power_integrable μ hμ (r + 1)), integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have hd : (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

end Rhone.Statistics.ThreeSiteSeparator
