/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederSource
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Gaussian product density and integration by parts

Source: lande_arnold1983, pp. 1212–1213, eq. 5b-9. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem standardGaussianPDF_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1
  · funext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rfl
  · simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Pi.pow_apply, Pi.neg_apply,
    id_eq]
    norm_num
    ring

theorem standardGaussian_integrable_iff (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * f x) volume := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  have h := integrable_withDensity_iff_integrable_smul' (g := f) (μ := volume)
    (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top (μ := 0) (v := 1)))
  simp only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)] at h
  convert h using 1
  rw [gaussianPDF_def]

theorem standardGaussian_stein (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf'm : Measurable f') (C D : ℝ) (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hfbound : ∀ x, |f x| ≤ C) (hf'bound : ∀ x, |f' x| ≤ D) :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hf
    x).continuousAt)).measurable
  have hfi : Integrable f (gaussianReal 0 1) :=
    (integrable_const C).mono' hfm.aestronglyMeasurable (Filter.Eventually.of_forall hfbound)
  have hf'i : Integrable f' (gaussianReal 0 1) :=
    (integrable_const D).mono' hf'm.aestronglyMeasurable (Filter.Eventually.of_forall hf'bound)
  have hxfi : Integrable (fun x => x * f x) (gaussianReal 0 1) := by
    apply (IsGaussian.integrable_id.norm.const_mul C).mono'
    · exact (measurable_id.mul hfm).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro x
      simp only [Real.norm_eq_abs, abs_mul, id_eq]
      nlinarith [abs_nonneg x, hfbound x]
  have hfg : Integrable (fun x => f x * gaussianPDFReal 0 1 x) volume := by
    simpa only [mul_comm] using (standardGaussian_integrable_iff f).mp hfi
  have hf'g : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) volume := by
    simpa only [mul_comm] using (standardGaussian_integrable_iff f').mp hf'i
  have hfg' : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) volume := by
    convert ((standardGaussian_integrable_iff (fun x => x * f x)).mp hxfi).neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (v := (1 : ℝ)) (B := ContinuousLinearMap.mul ℝ ℝ)
    hf'g hfg' hfg
    (fun x _ => by simpa using (hf x).hasFDerivAt.hasLineDerivAt (1 : ℝ))
    (fun x _ => by simpa using (standardGaussianPDF_hasDerivAt x).hasFDerivAt.hasLineDerivAt (1 :
      ℝ))
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  have heq : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      fun x => -(gaussianPDFReal 0 1 x * (x * f x)) := by funext x; ring
  change (∫ x, f x * (-x * gaussianPDFReal 0 1 x)) =
    -(∫ x, f' x * gaussianPDFReal 0 1 x) at hibp
  rw [heq, integral_neg, neg_inj] at hibp
  simpa only [smul_eq_mul, mul_comm] using hibp

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

def piStandardDensity (n : ℕ) (x : Fin n → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

theorem piStandardDensity_nonneg (n : ℕ) (x : Fin n → ℝ) : 0 ≤ piStandardDensity n x :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

theorem piStandardDensity_measurable (n : ℕ) : Measurable (piStandardDensity n) := by
  unfold piStandardDensity
  exact Finset.measurable_prod _ (fun i _ => (measurable_gaussianPDFReal 0 1).comp
    (measurable_pi_apply i))

theorem piGaussian_eq_density (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      volume.withDensity (fun x => ENNReal.ofReal (piStandardDensity n x)) := by
  apply Measure.pi_eq
  intro s hs
  have hi : Integrable (piStandardDensity n) (volume.restrict (Set.univ.pi s)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fin_nat_prod (fun _ => (integrable_gaussianPDFReal 0 1).restrict)
  calc
    _ = ENNReal.ofReal (∫ x in Set.univ.pi s, piStandardDensity n x) := by
      rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
      exact (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (piStandardDensity_nonneg n))).symm
    _ = ENNReal.ofReal (∏ i, ∫ x in s i, gaussianPDFReal 0 1 x) := by
      rw [volume_pi, Measure.restrict_pi_pi]
      congr 1
      exact integral_fintype_prod_eq_prod (fun _ : Fin n => gaussianPDFReal 0 1)
    _ = ∏ i, gaussianReal 0 1 (s i) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
        gaussianPDFReal_nonneg 0 1 x))]
      apply Finset.prod_congr rfl
      intro i _
      rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0), withDensity_apply _ (hs i),
        gaussianPDF_def]
      exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1 |>.restrict)
        (Filter.Eventually.of_forall (fun x => gaussianPDFReal_nonneg 0 1 x))

theorem piGaussian_integrable_iff (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    Integrable f (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) ↔
      Integrable (fun x => piStandardDensity n x * f x) volume := by
  rw [piGaussian_eq_density]
  have h := integrable_withDensity_iff_integrable_smul' (g := f) (μ := volume)
    ((piStandardDensity_measurable n).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
  simp only [ENNReal.toReal_ofReal (piStandardDensity_nonneg _ _)] at h
  convert h using 1

theorem piGaussian_integral (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∫ x, piStandardDensity n x * f x := by
  rw [piGaussian_eq_density, integral_withDensity_eq_integral_toReal_smul
    ((piStandardDensity_measurable n).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (piStandardDensity_nonneg _ _)]
  rfl

open MeasureTheory ProbabilityTheory

theorem piStandardDensity_hasLineDerivAt (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    HasLineDerivAt ℝ (piStandardDensity n) (-x i * piStandardDensity n x) x (Pi.single i 1) := by
  let p (j : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  let d (j : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ :=
    (-x j * gaussianPDFReal 0 1 (x j)) • p j
  have hj : ∀ j : Fin n, HasFDerivAt (fun y : Fin n → ℝ => gaussianPDFReal 0 1 (y j)) (d j) x := by
    intro j
    convert (standardGaussianPDF_hasDerivAt (x j)).hasFDerivAt.comp x
      (p j).hasFDerivAt using 1
    · rfl
    · ext y
      simp [d, p]
      ring
  have h := (HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hj j)).hasLineDerivAt
    (Pi.single i 1)
  have hc : (∏ j ∈ Finset.univ.erase i, gaussianPDFReal 0 1 (x j)) *
      (-x i * gaussianPDFReal 0 1 (x i)) = -x i * piStandardDensity n x := by
    rw [piStandardDensity, ← Finset.mul_prod_erase Finset.univ (fun j => gaussianPDFReal 0 1 (x
      j)) (Finset.mem_univ i)]
    ring
  convert h using 1
  · rfl
  · simpa [d, p, sum_apply, Pi.single_apply] using hc.symm

end Rhone.Statistics.GaussianBreeder
