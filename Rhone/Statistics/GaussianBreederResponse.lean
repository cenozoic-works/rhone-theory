/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederTransmission

/-!
# Nonlinear Gaussian Mendelian response

Source: lande_arnold1983, p. 1212, eq. 6b. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory

theorem gaussian_mendelian_nonlinear_response (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (hP : Matrix.det (G + E) ≠ 0) (w : V n → ℝ) (hw : Measurable w)
    (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (hwint : Integrable (fun q => w (gaussianPhenotype m q))
      (gaussianParentLaw n G E))
    (hzwint : Integrable (fun q => w (gaussianPhenotype m q) • gaussianPhenotype m q)
      (gaussianParentLaw n G E))
    (hbar : 0 < gaussianMeanFitness n G E w m) :
    (∫ z, z ∂gaussianOffspringLaw n G E w m) - m =
      Matrix.toEuclideanCLM (𝕜 := ℝ) G (gaussianSelectionGradient n G E w m) := by
  have hp := selectedParent_probability n G E w hw0 m hwint hbar
  have hc0 : ∀ i j, cov[fun q : GaussianParent n => q.1.1 i,
      fun q : GaussianParent n => (gaussianBreedingValue q + q.2) j;
      gaussianParentLaw n G E] = ((1 / 2 : ℝ) • G) i j := by
    intro i j
    rw [homologueZero_centeredPhenotype_covariance n G E hG]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hc1 : ∀ i j, cov[fun q : GaussianParent n => q.1.2 i,
      fun q : GaussianParent n => (gaussianBreedingValue q + q.2) j;
      gaussianParentLaw n G E] = ((1 / 2 : ℝ) • G) i j := by
    intro i j
    rw [homologueOne_centeredPhenotype_covariance n G E hG]
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have h0 := (selectedParent_linear_mean n G E ((1 / 2 : ℝ) • G) hG hE hP
    (homologueZeroCLM n) hc0 w hw hw0 m hwint hzwint hbar).1
  have h1 := (selectedParent_linear_mean n G E ((1 / 2 : ℝ) • G) hG hE hP
    (homologueOneCLM n) hc1 w hw hw0 m hwint hzwint hbar).1
  have hm := (offspring_mean n E (gaussianSelectedParentLaw n G E w m) h0 h1 m).2
  have ht : Measurable (fun p : GaussianParent n × Fin 2 => gaussianTransmittedHomologue p.1 p.2)
    := by
    unfold gaussianTransmittedHomologue
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      (by fun_prop) (by fun_prop)
  have ha : Measurable (fun p : (GaussianParent n × GaussianParent n) × ((Fin 2 × Fin 2) × V n) =>
      (p.1.1, p.2.1.1)) := measurable_fst.fst.prodMk measurable_snd.fst.fst
  have hb : Measurable (fun p : (GaussianParent n × GaussianParent n) × ((Fin 2 × Fin 2) × V n) =>
      (p.1.2, p.2.1.2)) := measurable_fst.snd.prodMk measurable_snd.fst.snd
  have hobs : Measurable (fun p : (GaussianParent n × GaussianParent n) × ((Fin 2 × Fin 2) × V n) =>
      m + gaussianTransmittedHomologue p.1.1 p.2.1.1 +
        gaussianTransmittedHomologue p.1.2 p.2.1.2 + p.2.2) :=
    ((measurable_const.add (ht.comp ha)).add (ht.comp hb)).add measurable_snd.snd
  unfold gaussianOffspringLaw
  rw [integral_map hobs.aemeasurable (by fun_prop), hm, add_sub_cancel_left]
  have hg := (selectedParent_linear_mean n G E G hG hE hP (breedingValueCLM n)
    (breedingValue_centeredPhenotype_covariance n G E hG) w hw hw0 m hwint hzwint hbar).2
  change (∫ q, gaussianBreedingValue q ∂gaussianSelectedParentLaw n G E w m) = _ at hg
  rw [hg]
  simp [gaussianSelectionGradient]

/-- Source: lande_arnold1983, p. 1212, eq. 2a-6b. -/
theorem gaussianOffspring_probability (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (hwint : Integrable (fun q => w (gaussianPhenotype m q)) (gaussianParentLaw n G E))
    (hbar : 0 < gaussianMeanFitness n G E w m) :
    IsProbabilityMeasure (gaussianOffspringLaw n G E w m) := by
  have := selectedParent_probability n G E w hw0 m hwint hbar
  unfold gaussianOffspringLaw
  infer_instance

end Rhone.Statistics.GaussianBreeder
