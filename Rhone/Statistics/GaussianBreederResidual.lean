/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederCovariance

/-!
# Independence of the Gaussian breeding residual

Source: lande_arnold1983, p. 1212, eq. 5b. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

def breedingResidualCLM (n : ℕ) (G E C : Matrix (Fin n) (Fin n) ℝ)
    (L : GaussianParent n →L[ℝ] V n) : GaussianParent n →L[ℝ] V n :=
  L - (Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)).comp (centeredPhenotypeCLM n)

theorem parentLinear_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (L : GaussianParent n →L[ℝ] V n) (i : Fin n) :
    MemLp (fun q => L q i) 2 (gaussianParentLaw n G E) :=
  (parentLinear_hasGaussianLaw n G E ((EuclideanSpace.proj i).comp L)).memLp_two

theorem matrix_centeredPhenotype_covariance (n : ℕ) (G E B : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (hE : E.PosSemidef) (i j : Fin n) :
    cov[fun q : GaussianParent n =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) B (gaussianBreedingValue q + q.2) i,
      fun q => (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] =
      (B * (G + E)) i j := by
  have heq : (fun q : GaussianParent n =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) B (gaussianBreedingValue q + q.2) i) =
      ∑ k : Fin n, fun q => B i k * (gaussianBreedingValue q + q.2) k := by
    funext q
    simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  rw [heq, covariance_sum_left]
  · simp_rw [covariance_const_mul_left, centeredPhenotype_covariance n G E hG hE]
    rfl
  · exact fun k => (centeredPhenotype_coordinate_memLp n G E k).const_mul _
  · exact centeredPhenotype_coordinate_memLp n G E j

theorem breedingResidual_covariance_zero (n : ℕ)
    (G E C : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (L : GaussianParent n →L[ℝ] V n)
    (hLC : ∀ i j, cov[fun q => L q i, fun q : GaussianParent n =>
      (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = C i j)
    (i j : Fin n) :
    cov[fun q => breedingResidualCLM n G E C L q i,
      fun q : GaussianParent n => (gaussianBreedingValue q + q.2) j;
        gaussianParentLaw n G E] = 0 := by
  change cov[(fun q : GaussianParent n => L q i) -
      (fun q => Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)
        (gaussianBreedingValue q + q.2) i),
      (fun q => (gaussianBreedingValue q + q.2) j); gaussianParentLaw n G E] = 0
  have hB : MemLp (fun q : GaussianParent n =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)
        (gaussianBreedingValue q + q.2) i) 2 (gaussianParentLaw n G E) := by
    simpa [centeredPhenotypeCLM, breedingValueCLM, homologueZeroCLM, homologueOneCLM,
      gaussianBreedingValue] using parentLinear_coordinate_memLp n G E
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)).comp (centeredPhenotypeCLM n)) i
  rw [covariance_sub_left (parentLinear_coordinate_memLp n G E L i) hB
    (centeredPhenotype_coordinate_memLp n G E j), hLC,
    matrix_centeredPhenotype_covariance n G E _ hG hE,
    Matrix.nonsing_inv_mul_cancel_right (G + E) C (isUnit_iff_ne_zero.mpr hP)]
  exact sub_self _

theorem breedingResidual_indep_centeredPhenotype (n : ℕ)
    (G E C : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (L : GaussianParent n →L[ℝ] V n)
    (hLC : ∀ i j, cov[fun q => L q i, fun q : GaussianParent n =>
      (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = C i j) :
    IndepFun (breedingResidualCLM n G E C L)
      (fun q : GaussianParent n => gaussianBreedingValue q + q.2) (gaussianParentLaw n G E) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hjoint := parentLinear_hasGaussianLaw n G E
    ((breedingResidualCLM n G E C L).prod (centeredPhenotypeCLM n))
  have hf := (hjoint.map_equiv (e.prodCongr e)).indepFun_of_covariance_eval
    (breedingResidual_covariance_zero n G E C hG hE hP L hLC)
  have hm : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → V n) := by fun_prop
  convert hf.comp hm hm using 1 <;> funext q <;> rfl

end Rhone.Statistics.GaussianBreeder
