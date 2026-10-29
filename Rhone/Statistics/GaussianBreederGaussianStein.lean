/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederStandardDensity
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Integration by parts for the multivariate Gaussian source

Source: lande_arnold1983, pp. 1212–1213, eq. 5b-9. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

theorem piGaussian_stein_coordinate (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (C D : ℝ)
    (hfbound : ∀ x, |f x| ≤ C) (hdbound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (i : Fin n) :
    (∫ x, x i * f x ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      ∫ x, fderiv ℝ f x (Pi.single i 1) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let df := fun x => fderiv ℝ f x (Pi.single i 1)
  have hdfm : Measurable df :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
  have hdfbound : ∀ x, |df x| ≤ D := by
    intro x
    calc
      _ ≤ ‖fderiv ℝ f x‖ * ‖Pi.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ D := by simpa [Pi.norm_single] using hdbound x
  have hfi : Integrable f μ := (integrable_const C).mono'
    hf.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hfbound)
  have hdfi : Integrable df μ := (integrable_const D).mono' hdfm.aestronglyMeasurable
    (Filter.Eventually.of_forall hdfbound)
  have hxi : Integrable (fun x : Fin n → ℝ => x i) μ := integrable_eval IsGaussian.integrable_id
  have hxfi : Integrable (fun x => x i * f x) μ := by
    apply (hxi.norm.const_mul C).mono'
    · exact ((measurable_pi_apply i).mul hf.continuous.measurable).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro x
      simp only [Real.norm_eq_abs, abs_mul]
      nlinarith [abs_nonneg (x i), hfbound x]
  have hfg : Integrable (fun x => f x * piStandardDensity n x) volume := by
    simpa only [mul_comm] using (piGaussian_integrable_iff n f).mp hfi
  have hf'g : Integrable (fun x => df x * piStandardDensity n x) volume := by
    simpa only [mul_comm] using (piGaussian_integrable_iff n df).mp hdfi
  have hfg' : Integrable (fun x => f x * (-x i * piStandardDensity n x)) volume := by
    convert ((piGaussian_integrable_iff n (fun x => x i * f x)).mp hxfi).neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (f := f) (f' := df) (g := piStandardDensity n)
    (g' := fun x => -x i * piStandardDensity n x)
    (v := Pi.single i (1 : ℝ)) (B := ContinuousLinearMap.mul ℝ ℝ)
    hf'g hfg' hfg
    (fun x _ => (hf.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _)
    (fun x _ => piStandardDensity_hasLineDerivAt n x i)
  change (∫ x, f x * (-x i * piStandardDensity n x)) = -(∫ x, df x * piStandardDensity n x) at hibp
  have heq : (fun x => f x * (-x i * piStandardDensity n x)) =
      fun x => -(piStandardDensity n x * (x i * f x)) := by funext x; ring
  rw [heq, integral_neg, neg_inj] at hibp
  rw [piGaussian_integral, piGaussian_integral]
  simpa only [mul_comm] using hibp

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem stdGaussian_stein_coordinate (n : ℕ) (f : V n → ℝ) (hf : ContDiff ℝ 1 f)
    (C D : ℝ) (hfbound : ∀ x, |f x| ≤ C) (hdbound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (i : Fin n) :
    (∫ x, x i * f x ∂stdGaussian (V n)) =
      ∫ x, fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) ∂stdGaussian (V n) := by
  let L : (Fin n → ℝ) →L[ℝ] V n := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n =>
    ℝ)).symm.toContinuousLinearMap
  let F := fun x => f (L x)
  have hF : ContDiff ℝ 1 F := hf.comp L.contDiff
  have hd (x : Fin n → ℝ) : fderiv ℝ F x = (fderiv ℝ f (L x)).comp L := by
    exact ((hf.differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  have hdb : ∀ x, ‖fderiv ℝ F x‖ ≤ D * ‖L‖ := by
    intro x
    rw [hd]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hdbound _)
      (norm_nonneg _))
  have hs := piGaussian_stein_coordinate n F hF C (D * ‖L‖) (fun x => hfbound _) hdb i
  have hfm : Measurable (fun x : V n => x i * f x) :=
    (EuclideanSpace.proj i).continuous.measurable.mul hf.continuous.measurable
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) hfm.aestronglyMeasurable,
    integral_map (by fun_prop) (by
      exact ((hf.continuous_fderiv (by simp)).clm_apply
        continuous_const).measurable.aestronglyMeasurable)]
  have he : L (Pi.single i 1) = EuclideanSpace.basisFun (Fin n) ℝ i := by
    rw [EuclideanSpace.basisFun_apply]
    rfl
  simp only [hd, ContinuousLinearMap.comp_apply, he] at hs
  convert hs using 1 <;> congr 1

theorem stdGaussian_stein_direction (n : ℕ) (f : V n → ℝ) (hf : ContDiff ℝ 1 f)
    (C D : ℝ) (hfbound : ∀ x, |f x| ≤ C) (hdbound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (v : V n) :
    (∫ x, ⟪v, x⟫ * f x ∂stdGaussian (V n)) =
      ∫ x, fderiv ℝ f x v ∂stdGaussian (V n) := by
  have hdfi : Integrable (fun x => fderiv ℝ f x) (stdGaussian (V n)) :=
    (integrable_const D).mono' (hf.continuous_fderiv (by simp)).measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hdbound)
  have hxi (i : Fin n) : Integrable (fun x : V n => x i * f x) (stdGaussian (V n)) := by
    have hi : Integrable (fun x : V n => x i) (stdGaussian (V n)) :=
      ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian (V n))).map_fun (EuclideanSpace.proj
        i)).integrable
    apply (hi.norm.const_mul C).mono'
    · exact ((EuclideanSpace.proj i).continuous.measurable.mul
      hf.continuous.measurable).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro x
      simp only [Real.norm_eq_abs, abs_mul]
      nlinarith [abs_nonneg (x i), hfbound x]
  have hl : (fun x : V n => ⟪v, x⟫ * f x) = fun x => ∑ i, v i * (x i * f x) := by
    funext x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hr : (fun x : V n => fderiv ℝ f x v) = fun x => ∑ i, v i * fderiv ℝ f x
    (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    funext x
    nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' v]
    simp only [map_sum, map_smul, EuclideanSpace.basisFun_inner, smul_eq_mul]
  rw [hl, hr, integral_finsetSum Finset.univ (fun i _ => (hxi i).const_mul (v i)),
    integral_finsetSum Finset.univ (fun i _ => (hdfi.apply_continuousLinearMap _).const_mul (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_const_mul, stdGaussian_stein_coordinate n f hf C D hfbound
    hdbound]

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder

theorem multivariateGaussian_stein_direction (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (w : V n → ℝ) (hw : ContDiff ℝ 1 w) (m : V n)
    (C D : ℝ) (hwbound : ∀ x, |w x| ≤ C) (hdbound : ∀ x, ‖fderiv ℝ w x‖ ≤ D) (v : V n) :
    (∫ x, ⟪v, x⟫ * w (m + x) ∂multivariateGaussian 0 S) =
      ∫ x, fderiv ℝ w (m + x) (Matrix.toEuclideanCLM (𝕜 := ℝ) S v) ∂multivariateGaussian 0 S := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let F : V n → ℝ := fun x => w (m + A x)
  have hF : ContDiff ℝ 1 F := hw.comp (contDiff_const.add A.contDiff)
  have hd (x : V n) : fderiv ℝ F x = (fderiv ℝ w (m + A x)).comp A := by
    have hp : HasFDerivAt (fun y : V n => m + A y) A x := by
      convert (A.hasFDerivAt.const_add m) using 1
    exact ((hw.differentiable (by simp) (m + A x)).hasFDerivAt.comp x hp).fderiv
  have hdb : ∀ x, ‖fderiv ℝ F x‖ ≤ D * ‖A‖ := by
    intro x
    rw [hd]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hdbound _) (norm_nonneg _))
  have hs := stdGaussian_stein_direction n F hF C (D * ‖A‖) (fun _ => hwbound _) hdb (A v)
  have hsa : IsSelfAdjoint A := (CFC.sqrt_nonneg S).isSelfAdjoint.map _
  have haa : A.comp A = Matrix.toEuclideanCLM (𝕜 := ℝ) S := by
    rw [← ContinuousLinearMap.mul_def]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) *
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) = _
    rw [← map_mul, CFC.sqrt_mul_sqrt_self _ hS.nonneg]
  have hinner (x : V n) : ⟪A v, x⟫ = ⟪v, A x⟫ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hsa.adjoint_eq]
  simp only [hd, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply A A, haa,
    hinner] at hs
  have hfm : Measurable (fun x : V n => ⟪v, x⟫ * w (m + x)) := by
    exact (by fun_prop : Measurable (fun x : V n => ⟪v, x⟫)).mul
      (hw.continuous.measurable.comp (by fun_prop))
  have hdm : Measurable (fun x : V n => fderiv ℝ w (m + x) (Matrix.toEuclideanCLM (𝕜 := ℝ) S v)) :=
    (((hw.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const).measurable
  unfold multivariateGaussian
  rw [integral_map (by fun_prop) hfm.aestronglyMeasurable,
    integral_map (by fun_prop) hdm.aestronglyMeasurable]
  convert hs using 1 <;> congr 1 <;> funext x <;> simp only [zero_add] <;> rfl

end Rhone.Statistics.GaussianBreeder
