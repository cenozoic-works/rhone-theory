/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederConditional

/-!
# Nonlinear selection on the Gaussian parental source

Source: lande_arnold1983, p. 1212, eq. 2a-6a. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

theorem nonlinear_parentLinear_weighted_mean (n : ℕ)
    (G E C : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (L : GaussianParent n →L[ℝ] V n)
    (hLC : ∀ i j, cov[fun q => L q i, fun q : GaussianParent n =>
      (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = C i j)
    (w : V n → ℝ) (hw : Measurable w) (m : V n)
    (hwint : Integrable (fun q => w (gaussianPhenotype m q)) (gaussianParentLaw n G E))
    (hzwint : Integrable (fun q => w (gaussianPhenotype m q) • gaussianPhenotype m q)
      (gaussianParentLaw n G E)) :
    Integrable (fun q => w (gaussianPhenotype m q) • L q) (gaussianParentLaw n G E) ∧
      (∫ q, w (gaussianPhenotype m q) • L q ∂gaussianParentLaw n G E) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)
          (∫ q, w (gaussianPhenotype m q) • (gaussianPhenotype m q - m)
            ∂gaussianParentLaw n G E) := by
  let R := breedingResidualCLM n G E C L
  let K := Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)
  have hrint : Integrable R (gaussianParentLaw n G E) :=
    (parentLinear_hasGaussianLaw n G E R).integrable
  have hi := breedingResidual_indep_phenotype n G E C hG hE hP L hLC m
  have hwi := hi.symm.comp hw measurable_id
  have hwrint : Integrable (fun q => w (gaussianPhenotype m q) • R q)
      (gaussianParentLaw n G E) := hwi.integrable_smul hwint hrint
  have hwrmean : ∫ q, w (gaussianPhenotype m q) • R q ∂gaussianParentLaw n G E = 0 := by
    have h := hwi.integral_fun_smul_eq_smul_integral hwint.1 hrint.1
    change (∫ q, w (gaussianPhenotype m q) • R q ∂gaussianParentLaw n G E) =
      (∫ q, w (gaussianPhenotype m q) ∂gaussianParentLaw n G E) •
        (∫ q, R q ∂gaussianParentLaw n G E) at h
    rw [parentLinear_integral n G E R, smul_zero] at h
    exact h
  have hzint : Integrable (fun q => w (gaussianPhenotype m q) • (gaussianPhenotype m q - m))
      (gaussianParentLaw n G E) := by
    simp_rw [smul_sub]
    exact hzwint.sub (hwint.smul_const m)
  have hkint := K.integrable_comp hzint
  have heq : (fun q => w (gaussianPhenotype m q) • L q) =
      (fun q => w (gaussianPhenotype m q) • R q) +
        (fun q => K (w (gaussianPhenotype m q) • (gaussianPhenotype m q - m))) := by
    funext q
    simp only [Pi.add_apply, R, breedingResidualCLM, sub_apply,
      ContinuousLinearMap.comp_apply, gaussianPhenotype_sub_location,
      show centeredPhenotypeCLM n q = gaussianBreedingValue q + q.2 from rfl,
      smul_sub, map_smul]
    simp [K]
  constructor
  · rw [heq]
    exact hwrint.add hkint
  · rw [heq]
    change (∫ q, w (gaussianPhenotype m q) • R q +
      K (w (gaussianPhenotype m q) • (gaussianPhenotype m q - m))
      ∂gaussianParentLaw n G E) = _
    rw [integral_add hwrint hkint, hwrmean, zero_add]
    exact K.integral_comp_comm hzint

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem selectedParent_probability (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (hwint : Integrable (fun q => w (gaussianPhenotype m q)) (gaussianParentLaw n G E))
    (hbar : 0 < gaussianMeanFitness n G E w m) :
    IsProbabilityMeasure (gaussianSelectedParentLaw n G E w m) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [gaussianSelectedParentLaw, Measure.smul_apply, withDensity_apply,
    MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hwint (Filter.Eventually.of_forall (fun q => hw0 _))]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hbar)) ENNReal.ofReal_ne_top

theorem selectedParent_integrable {n : ℕ} (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) (f : GaussianParent n → V n)
    (hfi : Integrable (fun q => w (gaussianPhenotype m q) • f q) (gaussianParentLaw n G E)) :
    Integrable f (gaussianSelectedParentLaw n G E w m) := by
  unfold gaussianSelectedParentLaw
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hbar)))
  apply (integrable_withDensity_iff_integrable_smul'
    ((hw.comp (gaussianPhenotype_measurable n m)).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [Function.comp_apply, ENNReal.toReal_ofReal (hw0 _)] using hfi

theorem selectedParent_integral {n : ℕ} (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (f : GaussianParent n → V n) :
    (∫ q, f q ∂gaussianSelectedParentLaw n G E w m) =
      (gaussianMeanFitness n G E w m)⁻¹ •
        (∫ q, w (gaussianPhenotype m q) • f q ∂gaussianParentLaw n G E) := by
  unfold gaussianSelectedParentLaw
  rw [integral_smul_measure]
  have hd : Measurable (fun q : GaussianParent n => ENNReal.ofReal (w (gaussianPhenotype m q))) :=
    (hw.comp (gaussianPhenotype_measurable n m)).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (hw0 _)]
  congr 1
  congr 1
  exact ENNReal.toReal_ofReal (integral_nonneg (fun q => hw0 _))

theorem selectedParent_linear_mean (n : ℕ)
    (G E C : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (L : GaussianParent n →L[ℝ] V n)
    (hLC : ∀ i j, cov[fun q => L q i, fun q : GaussianParent n =>
      (gaussianBreedingValue q + q.2) j; gaussianParentLaw n G E] = C i j)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (hwint : Integrable (fun q => w (gaussianPhenotype m q)) (gaussianParentLaw n G E))
    (hzwint : Integrable (fun q => w (gaussianPhenotype m q) • gaussianPhenotype m q)
      (gaussianParentLaw n G E)) (hbar : 0 < gaussianMeanFitness n G E w m) :
    Integrable L (gaussianSelectedParentLaw n G E w m) ∧
      (∫ q, L q ∂gaussianSelectedParentLaw n G E w m) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (C * (G + E)⁻¹)
          (gaussianSelectionDifferential n G E w m) := by
  obtain ⟨hli, hlmean⟩ := nonlinear_parentLinear_weighted_mean n G E C hG hE hP L hLC w hw m hwint
    hzwint
  constructor
  · exact selectedParent_integrable G E w hw hw0 m hbar L hli
  · have := selectedParent_probability n G E w hw0 m hwint hbar
    have hzint := selectedParent_integrable G E w hw hw0 m hbar (gaussianPhenotype m) hzwint
    have hcenter : (∫ q, gaussianPhenotype m q - m ∂gaussianSelectedParentLaw n G E w m) =
        gaussianSelectionDifferential n G E w m := by
      rw [integral_sub hzint (integrable_const m)]
      simp [gaussianSelectionDifferential]
    rw [selectedParent_integral G E w hw hw0 m L, hlmean, ← hcenter,
      selectedParent_integral G E w hw hw0 m (fun q => gaussianPhenotype m q - m)]
    exact (map_smul _ _ _).symm

end Rhone.Statistics.GaussianBreeder
