/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.KernelPrimitive
public import Mathlib.MeasureTheory.Integral.Prod

/-! # A CDF-weighted kernel is nonpositive by its signed tail certificate -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator

def cdfKernel (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y in Icc 0 x, μ.real (Iic y) * kernel x y

lemma cutoff_kernel_nonpos (x z : ℝ) (hz : 0 ≤ z) :
    (∫ y in Icc 0 x, if z ≤ y then kernel x y else 0) ≤ 0 := by
  have he : (fun y => if z ≤ y then kernel x y else 0) =
      (Ici z).indicator (kernel x) := rfl
  rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hs : Ici z ∩ Icc 0 x = Icc z x := by
    ext y
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hz.trans h.1, h.2⟩
  rw [hs]
  by_cases hzx : z ≤ x
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hzx]
    exact integral_kernel_nonpos hz hzx
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hzx)]

lemma joint_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then kernel x p.1 else 0)
      ((volume.restrict (Icc 0 x)).prod μ) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (K := Icc (0 : ℝ) x) (kernel_continuous x).norm.continuousOn
  have hm : Measurable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then kernel x p.1 else 0) :=
    ((kernel_continuous x).measurable.comp measurable_fst).ite
      (by measurability) measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable (max M 0)
  have hp : ∀ᵐ y ∂volume.restrict (Icc (0 : ℝ) x), y ∈ Icc 0 x :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp] with p hp
  split_ifs
  · exact (hM ⟨p.1, hp, rfl⟩).trans (le_max_left M 0)
  · simpa only [norm_zero] using le_max_right M 0

lemma cdfKernel_eq_swapped (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    cdfKernel μ x = ∫ z, (∫ y in Icc 0 x, if z ≤ y then kernel x y else 0) ∂μ := by
  have hinner (y : ℝ) :
      (∫ z, if z ≤ y then kernel x y else 0 ∂μ) = μ.real (Iic y) * kernel x y := by
    change (∫ z, (Iic y).indicator (fun _ => kernel x y) z ∂μ) = _
    rw [integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul]
  unfold cdfKernel
  simp_rw [← hinner]
  exact integral_integral_swap (joint_kernel_integrable μ x)

theorem cdfKernel_nonpos (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, 0 ≤ z) (x : ℝ) : cdfKernel μ x ≤ 0 := by
  rw [cdfKernel_eq_swapped]
  apply integral_nonpos_of_ae
  filter_upwards [hμ] with z hz
  exact cutoff_kernel_nonpos x z hz

end Rhone.Statistics.ThreeSiteSeparator
