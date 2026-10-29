/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederGaussianStein
public import Rhone.Statistics.GaussianBreederPhenotypeLaw
public import Rhone.Statistics.GaussianBreederConditional

/-!
# Gaussian phenotype score identity

Source: lande_arnold1983, pp. 1212–1213, eq. 5b-9. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

theorem phenotypeGaussian_stein_score (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (hE : E.PosSemidef) (hP : Matrix.det (G + E) ≠ 0)
    (w : V n → ℝ) (hw : ContDiff ℝ 1 w) (m : V n) (C : ℝ)
    (hwbound : ∀ z, |w z| ≤ C) (hdbound : ∀ z, ‖fderiv ℝ w z‖ ≤ C) (v : V n) :
    (∫ q, ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (G + E)⁻¹ v, gaussianPhenotype m q - m⟫ *
      w (gaussianPhenotype m q) ∂gaussianParentLaw n G E) =
      ∫ q, fderiv ℝ w (gaussianPhenotype m q) v ∂gaussianParentLaw n G E := by
  let K := Matrix.toEuclideanCLM (𝕜 := ℝ) (G + E)⁻¹
  have hPK : Matrix.toEuclideanCLM (𝕜 := ℝ) (G + E) (K v) = v := by
    rw [← ContinuousLinearMap.comp_apply]
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (G + E) * Matrix.toEuclideanCLM (𝕜 := ℝ) (G + E)⁻¹) v = v
    rw [← map_mul, Matrix.mul_nonsing_inv (G + E) (isUnit_iff_ne_zero.mpr hP)]
    simp
  have hs := multivariateGaussian_stein_direction n (G + E) (hG.add hE) w hw m C C hwbound hdbound
    (K v)
  rw [hPK, ← centeredPhenotype_law n G E hG hE] at hs
  have hfm : Measurable (fun x : V n => ⟪K v, x⟫ * w (m + x)) := by
    exact (by fun_prop : Measurable (fun x : V n => ⟪K v, x⟫)).mul
      (hw.continuous.measurable.comp (by fun_prop))
  have hdm : Measurable (fun x : V n => fderiv ℝ w (m + x) v) :=
    (((hw.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const).measurable
  rw [integral_map (by fun_prop) hfm.aestronglyMeasurable,
    integral_map (by fun_prop) hdm.aestronglyMeasurable] at hs
  convert hs using 1
  · congr 1
    funext q
    simp [K, gaussianPhenotype, centeredPhenotypeCLM,
      breedingValueCLM, homologueZeroCLM, homologueOneCLM, gaussianBreedingValue, add_assoc]
  · congr 1
    funext q
    simp [gaussianPhenotype, centeredPhenotypeCLM, breedingValueCLM,
      homologueZeroCLM, homologueOneCLM, gaussianBreedingValue, add_assoc]

end Rhone.Statistics.GaussianBreeder
