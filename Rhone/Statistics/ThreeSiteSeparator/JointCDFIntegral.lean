/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.CDFPowerIntegral

/-! # Bivariate layer-cake integrals on the unit square -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

def unitSquareVolume : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))

def rectangleCDF (ν : Measure (ℝ × ℝ)) (x : ℝ × ℝ) : ℝ :=
  ν.real (Iic x.1 ×ˢ Iic x.2)

def tailProductKernel (r s : ℕ) (x z : ℝ × ℝ) : ℝ :=
  (x.1^r*below x.1 z.1)*(x.2^s*below x.2 z.2)

def weightedJointCDF (r s : ℕ) (ν : Measure (ℝ × ℝ)) : ℝ :=
  ∫ x, x.1^r*x.2^s*rectangleCDF ν x ∂unitSquareVolume

lemma tailProduct_mean (ν : Measure (ℝ × ℝ)) (r s : ℕ) (x : ℝ × ℝ) :
    (∫ z, tailProductKernel r s x z ∂ν) = x.1^r*x.2^s*rectangleCDF ν x := by
  have he : tailProductKernel r s x =
      (Iic x.1 ×ˢ Iic x.2).indicator (fun _ => x.1^r*x.2^s) := by
    funext z
    simp only [tailProductKernel, below, indicator_apply, mem_prod, mem_Iic]
    by_cases h1 : z.1 ≤ x.1 <;> by_cases h2 : z.2 ≤ x.2 <;> simp [h1, h2]
  rw [he, integral_indicator (measurableSet_Iic.prod measurableSet_Iic), setIntegral_const]
  simp only [smul_eq_mul, rectangleCDF]
  ring

lemma unitSquareVolume_support :
    ∀ᵐ x ∂unitSquareVolume, x.1 ∈ Icc (0 : ℝ) 1 ∧ x.2 ∈ Icc (0 : ℝ) 1 := by
  have hs : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1), x ∈ Icc 0 1 :=
    ae_restrict_mem measurableSet_Icc
  exact (Measure.quasiMeasurePreserving_fst.ae hs).and
    (Measure.quasiMeasurePreserving_snd.ae hs)

lemma tailProduct_joint_integrable (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν] (r s : ℕ) :
    Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => tailProductKernel r s p.1 p.2)
      (unitSquareVolume.prod ν) := by
  let : IsFiniteMeasure unitSquareVolume := by unfold unitSquareVolume; infer_instance
  have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => tailProductKernel r s p.1 p.2) := by
    have h1 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => below p.1.1 p.2.1) := by
      unfold below
      exact measurable_const.ite (by measurability) measurable_const
    have h2 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => below p.1.2 p.2.2) := by
      unfold below
      exact measurable_const.ite (by measurability) measurable_const
    exact ((measurable_fst.comp measurable_fst).pow_const r |>.mul h1).mul
      ((measurable_snd.comp measurable_fst).pow_const s |>.mul h2)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae unitSquareVolume_support] with p hp
  have hbound (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (z : ℝ) :
      |x^n*below x z| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hx.1 n)]
    exact (mul_le_mul (pow_le_one₀ hx.1 hx.2) (below_abs_le_one _ _)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  rw [Real.norm_eq_abs, tailProductKernel, abs_mul]
  exact (mul_le_mul (hbound r hp.1 _) (hbound s hp.2 _) (abs_nonneg _) (by norm_num)).trans_eq
    (one_mul 1)

lemma tailProduct_cutoff_integral (r s : ℕ) {z : ℝ × ℝ}
    (hz : z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1) :
    (∫ x, tailProductKernel r s x z ∂unitSquareVolume) =
      ((1-z.1^(r+1))/((r : ℝ)+1))*((1-z.2^(s+1))/((s : ℝ)+1)) := by
  unfold unitSquareVolume tailProductKernel
  rw [integral_prod_mul (fun x => x^r*below x z.1) (fun x => x^s*below x z.2),
    cutoff_power_integral r hz.1, cutoff_power_integral s hz.2]

lemma weightedJointCDF_eq_tail_product (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 ∈ Icc (0 : ℝ) 1) (r s : ℕ) :
    weightedJointCDF r s ν =
      ∫ z, ((1-z.1^(r+1))/((r : ℝ)+1))*((1-z.2^(s+1))/((s : ℝ)+1)) ∂ν := by
  let : IsFiniteMeasure unitSquareVolume := by unfold unitSquareVolume; infer_instance
  unfold weightedJointCDF
  simp_rw [← tailProduct_mean ν]
  rw [integral_integral_swap (tailProduct_joint_integrable ν r s)]
  apply integral_congr_ae
  filter_upwards [hν] with z hz
  exact tailProduct_cutoff_integral r s hz

end Rhone.Statistics.ThreeSiteSeparator
