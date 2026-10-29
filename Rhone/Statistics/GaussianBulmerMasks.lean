/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.DiploidMendelianMarginal
public import Rhone.Statistics.GaussianBreederTransmission
public import Rhone.Statistics.GaussianBulmerDifference

/-!
# Gaussian-input diploid free-assortment moments

Source: bulmer1971, eq. (17), p. 206; bulmer1974, p. 282; turelli2017_infinitesimal, sec. 4, p. 48.
-/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory GaussianBreeder Probability.DiploidMarginalSelection
open scoped ENNReal

def maskSign {n : ℕ} (b : Fin n → Fin 2) (i : Fin n) : ℝ := if b i=0 then 1 else -1

theorem maskSign_mean (n : ℕ) (i : Fin n) :
    (∫ b, maskSign b i ∂meiosisMaskLaw n) = 0 := by
  have hm : Measurable (fun c : Fin 2 => if c=0 then (1:ℝ) else -1) :=
    measurable_of_countable _
  have hev : Measurable (fun b : Fin n → Fin 2 => b i) := measurable_pi_apply i
  change (∫ b, (if b i=0 then (1:ℝ) else -1) ∂meiosisMaskLaw n) = 0
  rw [← integral_map hev.aemeasurable hm.aestronglyMeasurable,
    meiosisMaskLaw_eval]
  rw [PMF.integral_eq_sum]
  norm_num [Fin.sum_univ_two, PMF.uniformOfFintype_apply, smul_eq_mul]

theorem maskSign_memLp (n : ℕ) (i : Fin n) :
    MemLp (fun b => maskSign b i) 2 (meiosisMaskLaw n) := by
  apply MemLp.of_bound (by unfold maskSign; fun_prop) 1
  exact Filter.Eventually.of_forall (fun b => by
    unfold maskSign
    split <;> norm_num)

theorem maskSign_product (n : ℕ) (i j : Fin n) :
    (∫ b, maskSign b i * maskSign b j ∂meiosisMaskLaw n) = if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    have heq : (fun b : Fin n → Fin 2 => maskSign b i * maskSign b i) = fun _ => (1:ℝ) := by
      funext b
      unfold maskSign
      split <;> norm_num
    rw [heq]
    simp
  · have hi : iIndepFun (fun i : Fin n => fun b : Fin n → Fin 2 => maskSign b i)
        (meiosisMaskLaw n) := by
      exact iIndepFun_pi (fun _ => (measurable_of_countable
        (fun c : Fin 2 => if c=0 then (1:ℝ) else -1)).aemeasurable)
    rw [(hi.indepFun hij).integral_fun_mul_eq_mul_integral
      (maskSign_memLp n i).aestronglyMeasurable (maskSign_memLp n j).aestronglyMeasurable,
      maskSign_mean, maskSign_mean]
    simp [hij]

def freelyTransmitted {n : ℕ} (q : GaussianParent n) (b : Fin n → Fin 2) : V n :=
  WithLp.toLp 2 (fun i => if b i=0 then q.1.1 i else q.1.2 i)

theorem freelyTransmitted_measurable (n : ℕ) :
    Measurable (fun p : GaussianParent n × (Fin n → Fin 2) => freelyTransmitted p.1 p.2) := by
  unfold freelyTransmitted
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply measurable_pi_iff.mpr
  intro i
  have h0 : Measurable (fun p : GaussianParent n × (Fin n → Fin 2) => p.1.1.1 i) := by fun_prop
  have h1 : Measurable (fun p : GaussianParent n × (Fin n → Fin 2) => p.1.1.2 i) := by fun_prop
  exact h0.ite (measurableSet_eq.preimage ((measurable_pi_apply i).comp measurable_snd)) h1

theorem freelyTransmitted_coordinate (n : ℕ) (q : GaussianParent n)
    (b : Fin n → Fin 2) (i : Fin n) :
    freelyTransmitted q b i =
      (gaussianBreedingValue q i+maskSign b i*homologueDifference q i)/2 := by
  by_cases hb : b i=0
  all_goals
    (simp [freelyTransmitted, gaussianBreedingValue, homologueDifference, maskSign, hb]; try ring)

theorem mask_linear_mean (n : ℕ) (i : Fin n) (a b : ℝ) :
    (∫ c, (a+maskSign c i*b)/2 ∂meiosisMaskLaw n) = a/2 := by
  rw [integral_div, integral_add (integrable_const a) Integrable.of_finite,
    integral_mul_const, maskSign_mean]
  simp

theorem mask_linear_second (n : ℕ) (i j : Fin n) (a b c d : ℝ) :
    (∫ z, ((a+maskSign z i*b)/2)*((c+maskSign z j*d)/2) ∂meiosisMaskLaw n) =
      (a*c+if i=j then b*d else 0)/4 := by
  have heq : (fun z : Fin n → Fin 2 => ((a+maskSign z i*b)/2)*((c+maskSign z j*d)/2)) =
      fun z => (a*c+a*d*maskSign z j+b*c*maskSign z i+b*d*(maskSign z i*maskSign z j))/4 := by
    funext z; ring
  rw [heq, integral_div]
  simp only [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, maskSign_mean, maskSign_product, integral_const, probReal_univ,
    smul_eq_mul, one_mul, mul_zero, add_zero]
  split_ifs <;> simp

theorem freelyTransmitted_mask_mean (n : ℕ) (q : GaussianParent n) (i : Fin n) :
    (∫ b, freelyTransmitted q b i ∂meiosisMaskLaw n) = gaussianBreedingValue q i/2 := by
  simp_rw [freelyTransmitted_coordinate]
  exact mask_linear_mean n i _ _

theorem freelyTransmitted_mask_second (n : ℕ) (q : GaussianParent n) (i j : Fin n) :
    (∫ b, freelyTransmitted q b i * freelyTransmitted q b j ∂meiosisMaskLaw n) =
      (gaussianBreedingValue q i * gaussianBreedingValue q j +
        if i=j then homologueDifference q i*homologueDifference q j else 0)/4 := by
  simp_rw [freelyTransmitted_coordinate]
  exact mask_linear_second n i j _ _ _ _

end Rhone.Statistics.GaussianBulmer
