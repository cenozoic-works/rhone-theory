/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBulmerDifference

/-!
# Gaussian-input diploid free-assortment moments

Source: bulmer1971, eq. (17), p. 206; bulmer1974, p. 282; turelli2017_infinitesimal, sec. 4, p. 48.
-/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory GaussianBreeder
open scoped ENNReal

theorem bounded_fitness_integrable (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n) :
    Integrable (fun q => w (gaussianPhenotype m q)) (gaussianParentLaw n G E) := by
  apply Integrable.of_bound (hw.comp (gaussianPhenotype_measurable n m)).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun q => by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
      using hwC (gaussianPhenotype m q))

theorem selected_measure_le (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n) :
    gaussianSelectedParentLaw n G E w m ≤
      ((ENNReal.ofReal (gaussianMeanFitness n G E w m))⁻¹ * ENNReal.ofReal C) •
        gaussianParentLaw n G E := by
  unfold gaussianSelectedParentLaw
  calc
    _ ≤ (ENNReal.ofReal (gaussianMeanFitness n G E w m))⁻¹ •
      (gaussianParentLaw n G E).withDensity (fun _ => ENNReal.ofReal C) := by
      gcongr
      exact withDensity_mono (Filter.Eventually.of_forall (fun q =>
        ENNReal.ofReal_le_ofReal (hwC _)))
    _ = _ := by rw [withDensity_const, smul_smul]

theorem selected_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) (f : GaussianParent n → ℝ)
    (hf : MemLp f 2 (gaussianParentLaw n G E)) :
    MemLp f 2 (gaussianSelectedParentLaw n G E w m) := by
  exact hf.of_measure_le_smul
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hbar)))
      ENNReal.ofReal_ne_top) (selected_measure_le n G E w C hwC m)

theorem selected_difference_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (m : V n) (hbar : 0 < gaussianMeanFitness n G E w m) (i j : Fin n) :
    cov[fun q => homologueDifference q i, fun q => homologueDifference q j;
      gaussianSelectedParentLaw n G E w m] = G i j := by
  simp only [covariance, selected_difference_integral_zero n G E hG w hw hw0 m hbar,
    sub_zero]
  exact selected_difference_product n G E hG w hw hw0 m hbar i j

theorem selected_breeding_difference_covariance_zero (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (C : ℝ) (hwC : ∀ z, w z ≤ C) (m : V n)
    (hbar : 0 < gaussianMeanFitness n G E w m) (i j : Fin n) :
    cov[fun q => gaussianBreedingValue q i, fun q => homologueDifference q j;
      gaussianSelectedParentLaw n G E w m] = 0 := by
  have hB := selected_coordinate_memLp n G E w C hwC m hbar _
    (breedingValue_coordinate_memLp n G E i)
  have hD := selected_coordinate_memLp n G E w C hwC m hbar _
    (difference_coordinate_memLp n G E j)
  have := selectedParent_probability n G E w hw0 m
    (bounded_fitness_integrable n G E w hw hw0 C hwC m) hbar
  rw [covariance_eq_sub hB hD, selected_difference_integral_zero n G E hG w hw hw0 m hbar]
  simp only [Pi.mul_apply, mul_zero, sub_zero]
  exact selected_difference_breeding_product_zero n G E hG w hw hw0 m i j

end Rhone.Statistics.GaussianBulmer
