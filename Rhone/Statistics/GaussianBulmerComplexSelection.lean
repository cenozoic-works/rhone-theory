/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.GaussianBulmerVariance
public import Rhone.Statistics.GaussianBulmerMaskLaplace
public import Mathlib.Probability.Independence.CharacteristicFunction
/-!
# Normalized phenotype selection preserves the difference product factorization

Source: bulmer1971, eq. (6)–(7), p. 203; bulmer1974, p. 282; turelli2017_infinitesimal, §4, p. 48.
-/
@[expose] public section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory GaussianBreeder Probability.DiploidMarginalSelection
open scoped ENNReal
theorem selected_complex_integral (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (f : GaussianParent n → ℂ) :
    (∫ q, f q ∂gaussianSelectedParentLaw n G E w m) =
      Complex.ofReal ((gaussianMeanFitness n G E w m)⁻¹) *
        (∫ q, Complex.ofReal (w (gaussianPhenotype m q)) * f q
          ∂gaussianParentLaw n G E) := by
  unfold gaussianSelectedParentLaw
  rw [integral_smul_measure]
  have hd : Measurable (fun q : GaussianParent n => ENNReal.ofReal (w (gaussianPhenotype m q))) :=
    (hw.comp (gaussianPhenotype_measurable n m)).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (hw0 _)]
  rw [ENNReal.toReal_ofReal (show 0 ≤ gaussianMeanFitness n G E w m from
    integral_nonneg (fun q => hw0 _))]
  simp only [Complex.real_smul]
theorem selected_difference_complex_product (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (F : V n × V n → ℂ) (hF : Measurable F)
    (H : V n → ℂ) (hH : Measurable H) :
    (∫ q, F (gaussianBreedingValue q, q.2) * H (homologueDifference q)
      ∂gaussianSelectedParentLaw n G E w m) =
      (∫ q, F (gaussianBreedingValue q, q.2)
        ∂gaussianSelectedParentLaw n G E w m) *
      (∫ q, H (homologueDifference q) ∂gaussianParentLaw n G E) := by
  have hi := difference_indep_breeding_environment n G E hG
  have hwm : Measurable (fun p : V n × V n =>
      Complex.ofReal (w (m + p.1 + p.2)) * F p) := by fun_prop
  have hym : Measurable (fun q : GaussianParent n => (gaussianBreedingValue q, q.2)) := by
    unfold gaussianBreedingValue; fun_prop
  have hdm : Measurable (homologueDifference (n := n)) := by
    unfold homologueDifference; fun_prop
  have hind := hi.symm.comp hwm hH
  rw [selected_complex_integral n G E w hw hw0 m,
    selected_complex_integral n G E w hw hw0 m]
  have h := hind.integral_fun_mul_eq_mul_integral
    (hwm.comp hym).aestronglyMeasurable (hH.comp hdm).aestronglyMeasurable
  change (∫ q, (Complex.ofReal (w (gaussianPhenotype m q)) * F (gaussianBreedingValue q, q.2)) *
      H (homologueDifference q) ∂gaussianParentLaw n G E) =
    (∫ q, Complex.ofReal (w (gaussianPhenotype m q)) * F (gaussianBreedingValue q, q.2)
      ∂gaussianParentLaw n G E) *
    (∫ q, H (homologueDifference q) ∂gaussianParentLaw n G E) at h
  simp_rw [← mul_assoc]
  rw [h]
  ring
end Rhone.Statistics.GaussianBulmer
