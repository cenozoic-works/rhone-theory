/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.GaussianBreederResponse

/-!
# Scalar breeder response with variance-ratio heritability

Source: lande_arnold1983, pp. 1212–1213, eq. 5a–6b. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

def scalarHeritability (G E : Matrix (Fin 1) (Fin 1) Real) : Real :=
  variance (fun q : GaussianParent 1 => gaussianBreedingValue q 0)
      (gaussianParentLaw 1 G E) /
    variance (fun q : GaussianParent 1 => (gaussianBreedingValue q + q.2) 0)
      (gaussianParentLaw 1 G E)

theorem scalarHeritability_eq (G E : Matrix (Fin 1) (Fin 1) Real)
    (hG : G.PosSemidef) (hE : E.PosSemidef) :
    scalarHeritability G E = G 0 0 / (G 0 0 + E 0 0) := by
  unfold scalarHeritability
  rw [← covariance_self (breedingValue_coordinate_memLp 1 G E 0).aemeasurable,
    breedingValue_covariance 1 G E hG,
    ← covariance_self (centeredPhenotype_coordinate_memLp 1 G E 0).aemeasurable,
    centeredPhenotype_covariance 1 G E hG hE]
  rfl

theorem gaussian_mendelian_scalar_response (G E : Matrix (Fin 1) (Fin 1) Real)
    (hG : G.PosSemidef) (hE : E.PosSemidef) (hP : Matrix.det (G + E) ≠ 0)
    (w : V 1 → Real) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (m : V 1)
    (hwint : Integrable (fun q => w (gaussianPhenotype m q)) (gaussianParentLaw 1 G E))
    (hzwint : Integrable (fun q => w (gaussianPhenotype m q) • gaussianPhenotype m q)
      (gaussianParentLaw 1 G E))
    (hbar : 0 < gaussianMeanFitness 1 G E w m) :
    ((∫ z, z ∂gaussianOffspringLaw 1 G E w m) - m) 0 =
      scalarHeritability G E * (gaussianSelectionDifferential 1 G E w m) 0 := by
  have h := congrArg (fun v : V 1 => v 0)
    (gaussian_mendelian_nonlinear_response 1 G E hG hE hP w hw hw0 m hwint hzwint hbar)
  rw [scalarHeritability_eq G E hG hE]
  simpa [gaussianSelectionGradient, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec,
    dotProduct, Fin.sum_univ_one, Matrix.inv_subsingleton, Ring.inverse_eq_inv,
    div_eq_mul_inv, mul_assoc] using h

end Rhone.Statistics.GaussianBreeder
