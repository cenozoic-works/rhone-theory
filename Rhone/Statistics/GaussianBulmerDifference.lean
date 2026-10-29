/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederCovariance
public import Rhone.Statistics.GaussianBreederSelection

/-!
# Gaussian-input diploid free-assortment moments

Source: bulmer1971, eq. (17), p. 206; bulmer1974, p. 282; turelli2017_infinitesimal, sec. 4, p. 48.
-/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory GaussianBreeder
open scoped ENNReal

def homologueDifferenceCLM (n : ℕ) : GaussianParent n →L[ℝ] V n :=
  homologueZeroCLM n - homologueOneCLM n

def homologueDifference {n : ℕ} (q : GaussianParent n) : V n := q.1.1-q.1.2

theorem difference_coordinate_memLp (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : MemLp (fun q => homologueDifference q i) 2 (gaussianParentLaw n G E) :=
  (homologueZero_coordinate_memLp n G E i).sub (homologueOne_coordinate_memLp n G E i)

theorem difference_covariance (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (i j : Fin n) :
    cov[fun q => homologueDifference q i,
      fun q => homologueDifference q j; gaussianParentLaw n G E] = G i j := by
  change cov[(fun q : GaussianParent n => q.1.1 i) - (fun q => q.1.2 i),
    (fun q => q.1.1 j) - (fun q => q.1.2 j); gaussianParentLaw n G E] = _
  rw [covariance_sub_left (homologueZero_coordinate_memLp n G E i)
    (homologueOne_coordinate_memLp n G E i)
      ((homologueZero_coordinate_memLp n G E j).sub (homologueOne_coordinate_memLp n G E j)),
    covariance_sub_right (homologueZero_coordinate_memLp n G E i)
      (homologueZero_coordinate_memLp n G E j) (homologueOne_coordinate_memLp n G E j),
    covariance_sub_right (homologueOne_coordinate_memLp n G E i)
      (homologueZero_coordinate_memLp n G E j) (homologueOne_coordinate_memLp n G E j),
    homologueZero_covariance n G E hG, homologueOne_covariance n G E hG,
    homologues_cross_covariance n G E,
    covariance_comm (X := fun q : GaussianParent n => q.1.2 i) (Y := fun q => q.1.1 j),
    homologues_cross_covariance n G E]
  ring

theorem difference_breeding_covariance_zero (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (i j : Fin n) :
    cov[fun q => homologueDifference q i,
      fun q => gaussianBreedingValue q j; gaussianParentLaw n G E] = 0 := by
  change cov[(fun q : GaussianParent n => q.1.1 i) - (fun q => q.1.2 i),
    (fun q => q.1.1 j) + (fun q => q.1.2 j); gaussianParentLaw n G E] = _
  rw [covariance_sub_left (homologueZero_coordinate_memLp n G E i)
    (homologueOne_coordinate_memLp n G E i)
      ((homologueZero_coordinate_memLp n G E j).add (homologueOne_coordinate_memLp n G E j)),
    covariance_add_right (homologueZero_coordinate_memLp n G E i)
      (homologueZero_coordinate_memLp n G E j) (homologueOne_coordinate_memLp n G E j),
    covariance_add_right (homologueOne_coordinate_memLp n G E i)
      (homologueZero_coordinate_memLp n G E j) (homologueOne_coordinate_memLp n G E j),
    homologueZero_covariance n G E hG, homologueOne_covariance n G E hG,
    homologues_cross_covariance n G E,
    covariance_comm (X := fun q : GaussianParent n => q.1.2 i) (Y := fun q => q.1.1 j),
    homologues_cross_covariance n G E]
  ring

theorem difference_environment_covariance_zero (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    cov[fun q => homologueDifference q i,
      fun q : GaussianParent n => q.2 j; gaussianParentLaw n G E] = 0 := by
  change cov[(fun q : GaussianParent n => q.1.1 i) - (fun q => q.1.2 i),
    (fun q => q.2 j); gaussianParentLaw n G E] = _
  rw [covariance_sub_left (homologueZero_coordinate_memLp n G E i)
    (homologueOne_coordinate_memLp n G E i) (environment_coordinate_memLp n G E j),
    homologueZero_environment_covariance, homologueOne_environment_covariance]
  simp

theorem difference_indep_breeding_environment (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) :
    IndepFun homologueDifference
      (fun q : GaussianParent n => (gaussianBreedingValue q,q.2))
      (gaussianParentLaw n G E) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  let T : GaussianParent n →L[ℝ] (Fin 2 × Fin n → ℝ) :=
    ContinuousLinearMap.pi (fun j => if j.1 = 0 then
      (EuclideanSpace.proj j.2).comp (breedingValueCLM n) else
      (EuclideanSpace.proj j.2).comp (ContinuousLinearMap.snd ℝ (V n × V n) (V n)))
  have hj := parentLinear_hasGaussianLaw n G E
    ((e.toContinuousLinearMap.comp (homologueDifferenceCLM n)).prod T)
  have hi := hj.indepFun_of_covariance_eval (by
    intro i j
    rcases j with ⟨b,j⟩
    fin_cases b
    · exact difference_breeding_covariance_zero n G E hG i j
    · exact difference_environment_covariance_zero n G E i j)
  have hleft : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → V n) := by fun_prop
  have hright : Measurable (fun z : Fin 2 × Fin n → ℝ =>
      (WithLp.toLp 2 (fun i => z (0,i)), WithLp.toLp 2 (fun i => z (1,i)))) := by fun_prop
  convert hi.comp hleft hright using 1 <;> funext q <;> rfl

theorem selected_scalar_integral (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (m : V n)
    (f : GaussianParent n → ℝ) :
    (∫ q, f q ∂gaussianSelectedParentLaw n G E w m) =
      (gaussianMeanFitness n G E w m)⁻¹ *
        (∫ q, w (gaussianPhenotype m q) * f q ∂gaussianParentLaw n G E) := by
  unfold gaussianSelectedParentLaw
  rw [integral_smul_measure]
  have hd : Measurable (fun q : GaussianParent n => ENNReal.ofReal (w (gaussianPhenotype m q))) :=
    (hw.comp (gaussianPhenotype_measurable n m)).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  rw [ENNReal.toReal_ofReal (show 0 ≤ gaussianMeanFitness n G E w m from
    integral_nonneg (fun q => hw0 _))]

theorem difference_selected_integral (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (m : V n) (hbar : 0 < gaussianMeanFitness n G E w m)
    (f : V n → ℝ) (hf : Measurable f) :
    (∫ q, f (homologueDifference q) ∂gaussianSelectedParentLaw n G E w m) =
      ∫ q, f (homologueDifference q) ∂gaussianParentLaw n G E := by
  have hi := difference_indep_breeding_environment n G E hG
  have hwm : Measurable (fun p : V n × V n => w (m+p.1+p.2)) := by fun_prop
  have hym : Measurable (fun q : GaussianParent n => (gaussianBreedingValue q,q.2)) := by
    unfold gaussianBreedingValue; fun_prop
  have hdm : Measurable (homologueDifference (n := n)) := by
    unfold homologueDifference; fun_prop
  have hind := hi.symm.comp hwm hf
  rw [selected_scalar_integral n G E w hw hw0 m]
  have h := hind.integral_fun_mul_eq_mul_integral
    (hwm.comp hym).aestronglyMeasurable (hf.comp hdm).aestronglyMeasurable
  change (∫ q, w (gaussianPhenotype m q) * f (homologueDifference q)
      ∂gaussianParentLaw n G E) =
    gaussianMeanFitness n G E w m *
      (∫ q, f (homologueDifference q) ∂gaussianParentLaw n G E) at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hbar), one_mul]

theorem difference_integral_zero (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∫ q, homologueDifference q i ∂gaussianParentLaw n G E) = 0 :=
  parentLinear_integral n G E ((EuclideanSpace.proj i).comp (homologueDifferenceCLM n))

theorem selected_difference_integral_zero (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (m : V n) (hbar : 0 < gaussianMeanFitness n G E w m) (i : Fin n) :
    (∫ q, homologueDifference q i ∂gaussianSelectedParentLaw n G E w m) = 0 := by
  rw [difference_selected_integral n G E hG w hw hw0 m hbar (fun z => z i)
    (by fun_prop), difference_integral_zero]

theorem selected_difference_product (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (m : V n) (hbar : 0 < gaussianMeanFitness n G E w m) (i j : Fin n) :
    (∫ q, homologueDifference q i * homologueDifference q j
      ∂gaussianSelectedParentLaw n G E w m) = G i j := by
  rw [difference_selected_integral n G E hG w hw hw0 m hbar (fun z => z i*z j)
    (by fun_prop)]
  have hc := difference_covariance n G E hG i j
  simp only [covariance, difference_integral_zero, sub_zero] at hc
  exact hc

theorem difference_weighted_product (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (f : V n → ℝ) (hf : Measurable f)
    (g : V n × V n → ℝ) (hg : Measurable g) :
    (∫ q, g (gaussianBreedingValue q,q.2) * f (homologueDifference q)
      ∂gaussianParentLaw n G E) =
    (∫ q, g (gaussianBreedingValue q,q.2) ∂gaussianParentLaw n G E) *
      (∫ q, f (homologueDifference q) ∂gaussianParentLaw n G E) := by
  have hym : Measurable (fun q : GaussianParent n => (gaussianBreedingValue q,q.2)) := by
    unfold gaussianBreedingValue; fun_prop
  have hdm : Measurable (homologueDifference (n := n)) := by
    unfold homologueDifference; fun_prop
  have hind := (difference_indep_breeding_environment n G E hG).symm.comp hg hf
  exact hind.integral_fun_mul_eq_mul_integral (hg.comp hym).aestronglyMeasurable
    (hf.comp hdm).aestronglyMeasurable

theorem selected_difference_breeding_product_zero (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef)
    (w : V n → ℝ) (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z)
    (m : V n) (i j : Fin n) :
    (∫ q, gaussianBreedingValue q i * homologueDifference q j
      ∂gaussianSelectedParentLaw n G E w m) = 0 := by
  rw [selected_scalar_integral n G E w hw hw0 m]
  have hproj : Measurable (fun p : V n × V n => p.1 i) := by fun_prop
  have hwm : Measurable (fun p : V n × V n => w (m+p.1+p.2)*p.1 i) :=
    (hw.comp ((measurable_const.add measurable_fst).add measurable_snd)).mul hproj
  have heq : (fun q : GaussianParent n => w (gaussianPhenotype m q) *
      (gaussianBreedingValue q i * homologueDifference q j)) =
      (fun q => (w (gaussianPhenotype m q)*gaussianBreedingValue q i) *
        homologueDifference q j) := by funext q; ring
  rw [heq]
  have h := difference_weighted_product n G E hG (fun z => z j) (by fun_prop)
    (fun p : V n × V n => w (m+p.1+p.2)*p.1 i) hwm
  change (∫ q, (w (gaussianPhenotype m q)*gaussianBreedingValue q i) *
      homologueDifference q j ∂gaussianParentLaw n G E) = _ at h
  rw [h]
  change (gaussianMeanFitness n G E w m)⁻¹ *
    ((∫ q, w (gaussianPhenotype m q)*gaussianBreedingValue q i ∂gaussianParentLaw n G E) *
      (∫ q, homologueDifference q j ∂gaussianParentLaw n G E)) = 0
  rw [difference_integral_zero, mul_zero, mul_zero]

end Rhone.Statistics.GaussianBulmer
