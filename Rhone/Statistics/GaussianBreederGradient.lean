/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederFitnessDerivative
public import Rhone.Statistics.GaussianBreederPhenotypeStein
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Nonlinear Gaussian selection and mean-fitness gradients

Source: lande_arnold1983, pp. 1212–1213, eq. 5b-9. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem gaussian_nonlinear_average_fitness_gradient (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (w : V n → ℝ) (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ z, 0 ≤ w z) (C : ℝ) (hC : 0 ≤ C)
    (hwbound : ∀ z, |w z| ≤ C) (hdbound : ∀ z, ‖fderiv ℝ w z‖ ≤ C)
    (m : V n) (hbar : 0 < gaussianMeanFitness n G E w m) :
    innerSL ℝ (gaussianSelectionGradient n G E w m) =
      (gaussianMeanFitness n G E w m)⁻¹ •
        (∫ q, fderiv ℝ w (gaussianPhenotype m q) ∂gaussianParentLaw n G E) := by
  obtain ⟨hwint, hzwint⟩ := boundedGaussian_fitness_moments n G E w hw.continuous.measurable C
    hwbound m
  have hcenterint : Integrable (fun q => w (gaussianPhenotype m q) • (gaussianPhenotype m q - m))
      (gaussianParentLaw n G E) := by
    simp_rw [smul_sub]
    exact hzwint.sub (hwint.smul_const m)
  have hdi : Integrable (fun q => fderiv ℝ w (gaussianPhenotype m q)) (gaussianParentLaw n G E) :=
    (integrable_const C).mono
      (((hw.continuous_fderiv (by simp)).measurable.comp (gaussianPhenotype_measurable n
        m)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun q => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using hdbound (gaussianPhenotype m q)))
  let K := Matrix.toEuclideanCLM (𝕜 := ℝ) (G + E)⁻¹
  have hsa : IsSelfAdjoint K := (hG.add hE).isHermitian.inv.isSelfAdjoint.map _
  have hinner (a b : V n) : ⟪K a, b⟫ = ⟪K b, a⟫ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq, real_inner_comm]
  ext v
  simp only [innerSL_apply_apply, smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply hdi v,
    selectionGradient_weighted_center n G E w hw.continuous.measurable hw0 m hwint hzwint hbar,
    real_inner_smul_left]
  change (gaussianMeanFitness n G E w m)⁻¹ *
    ⟪K (∫ q, w (gaussianPhenotype m q) • (gaussianPhenotype m q - m) ∂gaussianParentLaw n G E), v⟫
      = _
  rw [hinner, ← integral_inner hcenterint (K v)]
  have heq : (fun q : GaussianParent n => ⟪K v, w (gaussianPhenotype m q) • (gaussianPhenotype m q
    - m)⟫) =
      fun q => ⟪K v, gaussianPhenotype m q - m⟫ * w (gaussianPhenotype m q) := by
    funext q
    rw [real_inner_smul_right, mul_comm]
  rw [heq, phenotypeGaussian_stein_score n G E hG hE hP w hw m C hwbound hdbound v]

theorem gaussian_nonlinear_log_mean_fitness_derivative (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (w : V n → ℝ) (hw : ContDiff ℝ 1 w)
    (hw0 : ∀ z, 0 ≤ w z) (C : ℝ) (hC : 0 ≤ C)
    (hwbound : ∀ z, |w z| ≤ C) (hdbound : ∀ z, ‖fderiv ℝ w z‖ ≤ C)
    (m : V n) (hbar : 0 < gaussianMeanFitness n G E w m) :
    HasFDerivAt (fun a => Real.log (gaussianMeanFitness n G E w a))
      (innerSL ℝ (gaussianSelectionGradient n G E w m)) m := by
  have hd := (gaussianMeanFitness_hasFDerivAt n G E w hw C hwbound hdbound m).log hbar.ne'
  rw [gaussian_nonlinear_average_fitness_gradient n G E hG hE hP w hw hw0 C hC hwbound hdbound m
    hbar]
  exact hd

end Rhone.Statistics.GaussianBreeder
