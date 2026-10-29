/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederSelection
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating nonlinear Gaussian mean fitness

Source: lande_arnold1983, pp. 1212–1213, eq. 5b-9. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

theorem gaussianMeanFitness_hasFDerivAt (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : ContDiff ℝ 1 w) (C : ℝ)
    (hwbound : ∀ z, |w z| ≤ C) (hdbound : ∀ z, ‖fderiv ℝ w z‖ ≤ C) (m : V n) :
    HasFDerivAt (gaussianMeanFitness n G E w)
      (∫ q, fderiv ℝ w (gaussianPhenotype m q) ∂gaussianParentLaw n G E) m := by
  have : IsProbabilityMeasure (gaussianParentLaw n G E) := by
    unfold gaussianParentLaw
    infer_instance
  have hd : Differentiable ℝ w := hw.differentiable (by simp)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun a q => w (gaussianPhenotype a q))
    (F' := fun a q => fderiv ℝ w (gaussianPhenotype a q))
    (s := Set.univ) (bound := fun _ => C) (by simp)
  · exact Filter.Eventually.of_forall (fun a => by
      have hm : Measurable (gaussianPhenotype a) := by
        unfold gaussianPhenotype gaussianBreedingValue
        fun_prop
      exact (hw.continuous.measurable.comp hm).aestronglyMeasurable)
  · apply (integrable_const C).mono'
    · have hm : Measurable (gaussianPhenotype m) := by
        unfold gaussianPhenotype gaussianBreedingValue
        fun_prop
      exact (hw.continuous.measurable.comp hm).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun q => hwbound _)
  · have hm : Measurable (gaussianPhenotype m) := by
      unfold gaussianPhenotype gaussianBreedingValue
      fun_prop
    exact ((hw.continuous_fderiv (by simp)).measurable.comp hm).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun q a _ => hdbound _)
  · exact integrable_const C
  · apply Filter.Eventually.of_forall
    intro q a _
    have hp : HasFDerivAt (fun b : V n => gaussianPhenotype b q)
        (ContinuousLinearMap.id ℝ (V n)) a := by
      convert
        ((hasFDerivAt_id a).add_const (gaussianBreedingValue q)).add_const q.2 using 1
      rfl
    convert (hd (gaussianPhenotype a q)).hasFDerivAt.comp a hp using 1
    · rfl
    · simp

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem boundedGaussian_fitness_moments (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (C : ℝ) (hwbound : ∀ z, |w z| ≤ C) (m : V n) :
    Integrable (fun q => w (gaussianPhenotype m q)) (gaussianParentLaw n G E) ∧
      Integrable (fun q => w (gaussianPhenotype m q) • gaussianPhenotype m q)
        (gaussianParentLaw n G E) := by
  have hwz := hw.comp (gaussianPhenotype_measurable n m)
  have hzi : Integrable (gaussianPhenotype m) (gaussianParentLaw n G E) := by
    convert (integrable_const m).add (centeredPhenotype_hasGaussianLaw n G E).integrable using 1
    funext q
    simp only [Pi.add_apply, gaussianPhenotype, add_assoc]
  constructor
  · exact (integrable_const C).mono' hwz.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hwbound _))
  · apply (hzi.norm.const_mul C).mono'
    · exact (hwz.smul (gaussianPhenotype_measurable n m)).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro q
      simp only [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hwbound _) (norm_nonneg _)

theorem selectionGradient_weighted_center (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (hwint : Integrable (fun q => w (gaussianPhenotype m q)) (gaussianParentLaw n G E))
    (hzwint : Integrable (fun q => w (gaussianPhenotype m q) • gaussianPhenotype m q)
      (gaussianParentLaw n G E)) (hbar : 0 < gaussianMeanFitness n G E w m) :
    gaussianSelectionGradient n G E w m =
      (gaussianMeanFitness n G E w m)⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) (G + E)⁻¹
        (∫ q, w (gaussianPhenotype m q) • (gaussianPhenotype m q - m) ∂gaussianParentLaw n G E) :=
          by
  have := selectedParent_probability n G E w hw0 m hwint hbar
  have hzint := selectedParent_integrable G E w hw hw0 m hbar (gaussianPhenotype m) hzwint
  have hcenter : (∫ q, gaussianPhenotype m q - m ∂gaussianSelectedParentLaw n G E w m) =
      gaussianSelectionDifferential n G E w m := by
    rw [integral_sub hzint (integrable_const m)]
    simp [gaussianSelectionDifferential]
  unfold gaussianSelectionGradient
  rw [← hcenter, selectedParent_integral G E w hw hw0 m (fun q => gaussianPhenotype m q - m),
    map_smul]

end Rhone.Statistics.GaussianBreeder
