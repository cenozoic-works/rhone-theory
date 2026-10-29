/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederResidual

/-!
# Gaussian conditional breeding-value mean

Source: lande_arnold1983, p. 1212, eq. 5b. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

theorem gaussianPhenotype_sub_location (n : ℕ) (m : V n) (q : GaussianParent n) :
    gaussianPhenotype m q - m = gaussianBreedingValue q + q.2 := by
  unfold gaussianPhenotype
  abel

theorem gaussianPhenotype_measurable (n : ℕ) (m : V n) :
    Measurable (gaussianPhenotype m) := by
  unfold gaussianPhenotype gaussianBreedingValue
  fun_prop

theorem breedingResidual_indep_phenotype (n : ℕ)
    (G E C : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (L : GaussianParent n →L[ℝ] V n)
    (hLC : ∀ i j, cov[fun q => L q i, fun q : GaussianParent n =>
      (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = C i j) (m : V n) :
    IndepFun (breedingResidualCLM n G E C L) (gaussianPhenotype m)
      (gaussianParentLaw n G E) := by
  have h := breedingResidual_indep_centeredPhenotype n G E C hG hE hP L hLC
  have hm : Measurable (fun x : V n => m + x) := by fun_prop
  have heq : gaussianPhenotype m = fun q => m + (gaussianBreedingValue q + q.2) := by
    funext q
    simp only [gaussianPhenotype, add_assoc]
  rw [heq]
  exact h.comp measurable_id hm

theorem parentLinear_conditional_mean (n : ℕ)
    (G E C : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (L : GaussianParent n →L[ℝ] V n)
    (hLC : ∀ i j, cov[fun q => L q i, fun q : GaussianParent n =>
      (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = C i j) (m : V n) :
    (gaussianParentLaw n G E)[L | MeasurableSpace.comap (gaussianPhenotype m) inferInstance]
      =ᵐ[gaussianParentLaw n G E]
        fun q => Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)
          (gaussianPhenotype m q - m) := by
  let μ := gaussianParentLaw n G E
  let R := breedingResidualCLM n G E C L
  let K := Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)
  let f : GaussianParent n → V n := fun q => K (gaussianPhenotype m q - m)
  have hz : Measurable (gaussianPhenotype m) := gaussianPhenotype_measurable n m
  have hM : MeasurableSpace.comap (gaussianPhenotype m) inferInstance ≤ (inferInstance :
    MeasurableSpace (GaussianParent n)) := hz.comap_le
  have hr : Measurable R := by fun_prop
  have hR : MeasurableSpace.comap R inferInstance ≤ (inferInstance : MeasurableSpace
    (GaussianParent n)) := hr.comap_le
  have hrm : @Measurable (GaussianParent n) (V n)
      (MeasurableSpace.comap R inferInstance) inferInstance R :=
    measurable_iff_comap_le.mpr le_rfl
  have hi := breedingResidual_indep_phenotype n G E C hG hE hP L hLC m
  have hc := condExp_indep_eq hR hM hrm.stronglyMeasurable
    ((IndepFun_iff_Indep R (gaussianPhenotype m) μ).mp hi)
  have hRmean : ∫ q, R q ∂μ = 0 := parentLinear_integral n G E R
  rw [hRmean] at hc
  have hzm : @Measurable (GaussianParent n) (V n) (MeasurableSpace.comap (gaussianPhenotype m)
    inferInstance) inferInstance
      (gaussianPhenotype m) := measurable_iff_comap_le.mpr le_rfl
  have hfm : StronglyMeasurable[MeasurableSpace.comap (gaussianPhenotype m) inferInstance] f :=
    (K.continuous.measurable.comp (hzm.sub_const m)).stronglyMeasurable
  have hf_eq : f = (K.comp (centeredPhenotypeCLM n) : GaussianParent n → V n) := by
    funext q
    simp [f, gaussianPhenotype_sub_location, centeredPhenotypeCLM, breedingValueCLM,
      homologueZeroCLM, homologueOneCLM, gaussianBreedingValue]
  have hfint : Integrable f μ := by
    rw [hf_eq]
    exact (parentLinear_hasGaussianLaw n G E (K.comp (centeredPhenotypeCLM n))).integrable
  have hrint : Integrable R μ := (parentLinear_hasGaussianLaw n G E R).integrable
  have hl_eq : (L : GaussianParent n → V n) = R + f := by
    funext q
    simp [R, f, breedingResidualCLM, gaussianPhenotype_sub_location, K,
      centeredPhenotypeCLM, breedingValueCLM, homologueZeroCLM, homologueOneCLM,
      gaussianBreedingValue]
  have hadd := condExp_add hrint hfint (MeasurableSpace.comap (gaussianPhenotype m) inferInstance)
  have hfcond := condExp_of_stronglyMeasurable hM hfm hfint
  rw [← hl_eq, hfcond] at hadd
  filter_upwards [hadd, hc] with q hq hcq
  simpa [hcq, f, μ, K] using hq

theorem gaussian_conditional_breeding_mean (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (m : V n) :
    (gaussianParentLaw n G E)[gaussianBreedingValue |
      MeasurableSpace.comap (gaussianPhenotype m) inferInstance] =ᵐ[gaussianParentLaw n G E]
      fun q => Matrix.toEuclideanCLM (𝕜 := ℝ) (G * (G + E)⁻¹)
        (gaussianPhenotype m q - m) := by
  exact parentLinear_conditional_mean n G E G hG hE hP (breedingValueCLM n)
    (breedingValue_centeredPhenotype_covariance n G E hG) m

end Rhone.Statistics.GaussianBreeder
