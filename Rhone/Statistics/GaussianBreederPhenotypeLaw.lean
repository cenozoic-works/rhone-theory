/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederCovariance
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# The Gaussian phenotype distribution

Source: lande_arnold1983, pp. 1212–1213, eq. 5b-9. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

theorem centeredPhenotype_law (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (hE : E.PosSemidef) :
    (gaussianParentLaw n G E).map (centeredPhenotypeCLM n) = multivariateGaussian 0 (G + E) := by
  have : IsGaussian ((gaussianParentLaw n G E).map (centeredPhenotypeCLM n)) :=
    (centeredPhenotype_hasGaussianLaw n G E).isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simpa only [id_eq, integral_id_multivariateGaussian] using parentLinear_integral n G E
      (centeredPhenotypeCLM n)
  · ext x y
    have hc := covarianceBilin_apply_pi (centeredPhenotype_coordinate_memLp n G E) x y
    change covarianceBilin ((gaussianParentLaw n G E).map (centeredPhenotypeCLM n)) x y = _ at hc
    rw [hc, covarianceBilin_multivariateGaussian (hG.add hE)]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum,
      centeredPhenotype_covariance n G E hG hE]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

end Rhone.Statistics.GaussianBreeder
