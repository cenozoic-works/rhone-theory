/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBreederSelection
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Fair Mendelian homologue transmission

Source: lande_arnold1983, p. 1212, eq. 6b. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBreeder
open MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev mendelianCoin := (PMF.uniformOfFintype (Fin 2)).toMeasure

def homologueWeight (b c : Fin 2) : ℝ := if b = c then 1 else 0

theorem homologueWeight_integral (c : Fin 2) :
    (∫ b, homologueWeight b c ∂mendelianCoin) = 1 / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp [homologueWeight, measureReal_def, mendelianCoin]

theorem reverse_smul_prod_integrable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] {n : ℕ} {f : α → V n} {a : β → ℝ}
    (hf : Integrable f μ) (ha : Integrable a ν) :
    Integrable (fun p : α × β => a p.2 • f p.1) (μ.prod ν) := by
  exact hf.op_fst_snd (op := fun x y => y • x) (by fun_prop)
    ⟨1, by intro x y; simp [norm_smul, mul_comm]⟩ ha

theorem reverse_smul_prod_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] {n : ℕ}
    (f : α → V n) (a : β → ℝ) :
    (∫ p : α × β, a p.2 • f p.1 ∂μ.prod ν) = (∫ b, a b ∂ν) • ∫ q, f q ∂μ := by
  rw [← integral_prod_swap]
  exact integral_prod_smul a f

theorem gaussianTransmittedHomologue_eq {n : ℕ} (q : GaussianParent n) (b : Fin 2) :
    gaussianTransmittedHomologue q b =
      homologueWeight b 0 • q.1.1 + homologueWeight b 1 • q.1.2 := by
  fin_cases b <;> simp [gaussianTransmittedHomologue, homologueWeight]

abbrev offspringNoiseLaw {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) :=
  (mendelianCoin.prod mendelianCoin).prod (multivariateGaussian 0 E)

theorem offspring_coin_weight_integral {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin 2) :
    (∫ p, homologueWeight p.1.1 c ∂offspringNoiseLaw E) = 1 / 2 ∧
      (∫ p, homologueWeight p.1.2 c ∂offspringNoiseLaw E) = 1 / 2 := by
  constructor
  · calc
      _ = ∫ p : Fin 2 × Fin 2, homologueWeight p.1 c ∂mendelianCoin.prod mendelianCoin := by
        simpa only [probReal_univ, one_smul] using
          integral_fun_fst (μ := mendelianCoin.prod mendelianCoin)
            (ν := multivariateGaussian (0 : V n) E) (fun p : Fin 2 × Fin 2 => homologueWeight p.1 c)
      _ = 1 / 2 := by
        simpa only [probReal_univ, one_smul, homologueWeight_integral] using
          integral_fun_fst (μ := mendelianCoin) (ν := mendelianCoin) (fun b => homologueWeight b c)
  · calc
      _ = ∫ p : Fin 2 × Fin 2, homologueWeight p.2 c ∂mendelianCoin.prod mendelianCoin := by
        simpa only [probReal_univ, one_smul] using
          integral_fun_fst (μ := mendelianCoin.prod mendelianCoin)
            (ν := multivariateGaussian (0 : V n) E) (fun p : Fin 2 × Fin 2 => homologueWeight p.2 c)
      _ = 1 / 2 := by
        simpa only [probReal_univ, one_smul, homologueWeight_integral] using
          integral_fun_snd (μ := mendelianCoin) (ν := mendelianCoin) (fun b => homologueWeight b c)

theorem offspring_mean (n : ℕ) (E : Matrix (Fin n) (Fin n) ℝ)
    (μ : Measure (GaussianParent n)) [IsProbabilityMeasure μ]
    (h0 : Integrable (fun q => q.1.1) μ) (h1 : Integrable (fun q => q.1.2) μ) (m : V n) :
    Integrable (fun p => m + gaussianTransmittedHomologue p.1.1 p.2.1.1 +
      gaussianTransmittedHomologue p.1.2 p.2.1.2 + p.2.2)
      ((μ.prod μ).prod (offspringNoiseLaw E)) ∧
    (∫ p, m + gaussianTransmittedHomologue p.1.1 p.2.1.1 +
      gaussianTransmittedHomologue p.1.2 p.2.1.2 + p.2.2
      ∂(μ.prod μ).prod (offspringNoiseLaw E)) = m + ∫ q, gaussianBreedingValue q ∂μ := by
  let ν := offspringNoiseLaw E
  have ha0 : Integrable (fun p : (Fin 2 × Fin 2) × V n => homologueWeight p.1.1 0) ν :=
    ((Integrable.of_finite : Integrable (fun b => homologueWeight b 0) mendelianCoin).comp_fst
      mendelianCoin).comp_fst (multivariateGaussian 0 E)
  have ha1 : Integrable (fun p : (Fin 2 × Fin 2) × V n => homologueWeight p.1.1 1) ν :=
    ((Integrable.of_finite : Integrable (fun b => homologueWeight b 1) mendelianCoin).comp_fst
      mendelianCoin).comp_fst (multivariateGaussian 0 E)
  have hb0 : Integrable (fun p : (Fin 2 × Fin 2) × V n => homologueWeight p.1.2 0) ν :=
    ((Integrable.of_finite : Integrable (fun b => homologueWeight b 0) mendelianCoin).comp_snd
      mendelianCoin).comp_fst (multivariateGaussian 0 E)
  have hb1 : Integrable (fun p : (Fin 2 × Fin 2) × V n => homologueWeight p.1.2 1) ν :=
    ((Integrable.of_finite : Integrable (fun b => homologueWeight b 1) mendelianCoin).comp_snd
      mendelianCoin).comp_fst (multivariateGaussian 0 E)
  have hi00 := reverse_smul_prod_integrable (μ.prod μ) ν (h0.comp_fst μ) ha0
  have hi01 := reverse_smul_prod_integrable (μ.prod μ) ν (h1.comp_fst μ) ha1
  have hi10 := reverse_smul_prod_integrable (μ.prod μ) ν (h0.comp_snd μ) hb0
  have hi11 := reverse_smul_prod_integrable (μ.prod μ) ν (h1.comp_snd μ) hb1
  have heint : Integrable (fun p : (GaussianParent n × GaussianParent n) × ((Fin 2 × Fin 2) × V n)
    => p.2.2)
      ((μ.prod μ).prod ν) := by
    exact (IsGaussian.integrable_id (μ := multivariateGaussian (0 : V n) E)).comp_snd
      (mendelianCoin.prod mendelianCoin) |>.comp_snd (μ.prod μ)
  constructor
  · simp_rw [gaussianTransmittedHomologue_eq]
    convert (((integrable_const m).add (hi00.add hi01)).add (hi10.add hi11)).add heint using 1
  · simp_rw [gaussianTransmittedHomologue_eq]
    have heq : (fun p : (GaussianParent n × GaussianParent n) × ((Fin 2 × Fin 2) × V n) =>
        m + (homologueWeight p.2.1.1 0 • p.1.1.1.1 + homologueWeight p.2.1.1 1 • p.1.1.1.2) +
        (homologueWeight p.2.1.2 0 • p.1.2.1.1 + homologueWeight p.2.1.2 1 • p.1.2.1.2) + p.2.2) =
      fun p => ((((m + homologueWeight p.2.1.1 0 • p.1.1.1.1) + homologueWeight p.2.1.1 1 •
        p.1.1.1.2) +
        homologueWeight p.2.1.2 0 • p.1.2.1.1) + homologueWeight p.2.1.2 1 • p.1.2.1.2) + p.2.2 :=
          by
      funext p; abel
    rw [heq]
    have hsum0 := integral_add (integrable_const m) hi00
    have hsum1 := integral_add ((integrable_const m).add hi00) hi01
    have hsum2 := integral_add (((integrable_const m).add hi00).add hi01) hi10
    have hsum3 := integral_add ((((integrable_const m).add hi00).add hi01).add hi10) hi11
    have hsum4 := integral_add (((((integrable_const m).add hi00).add hi01).add hi10).add hi11)
      heint
    simp only [Pi.add_apply] at hsum0 hsum1 hsum2 hsum3 hsum4
    rw [hsum4, hsum3, hsum2, hsum1, hsum0]
    simp only [integral_const, probReal_univ, one_smul]
    rw [reverse_smul_prod_integral (μ.prod μ) ν
        (fun q => q.1.1.1) (fun p => homologueWeight p.1.1 0),
      reverse_smul_prod_integral (μ.prod μ) ν
        (fun q => q.1.1.2) (fun p => homologueWeight p.1.1 1),
      reverse_smul_prod_integral (μ.prod μ) ν
        (fun q => q.2.1.1) (fun p => homologueWeight p.1.2 0),
      reverse_smul_prod_integral (μ.prod μ) ν
        (fun q => q.2.1.2) (fun p => homologueWeight p.1.2 1)]
    rw [(offspring_coin_weight_integral E 0).1, (offspring_coin_weight_integral E 1).1,
      (offspring_coin_weight_integral E 0).2, (offspring_coin_weight_integral E 1).2]
    have hf0 : (∫ q : GaussianParent n × GaussianParent n, q.1.1.1 ∂μ.prod μ) = ∫ q, q.1.1 ∂μ := by
      simpa only [probReal_univ, one_smul] using integral_fun_fst (μ := μ) (ν := μ) (fun q => q.1.1)
    have hf1 : (∫ q : GaussianParent n × GaussianParent n, q.1.1.2 ∂μ.prod μ) = ∫ q, q.1.2 ∂μ := by
      simpa only [probReal_univ, one_smul] using integral_fun_fst (μ := μ) (ν := μ) (fun q => q.1.2)
    have hs0 : (∫ q : GaussianParent n × GaussianParent n, q.2.1.1 ∂μ.prod μ) = ∫ q, q.1.1 ∂μ := by
      simpa only [probReal_univ, one_smul] using integral_fun_snd (μ := μ) (ν := μ) (fun q => q.1.1)
    have hs1 : (∫ q : GaussianParent n × GaussianParent n, q.2.1.2 ∂μ.prod μ) = ∫ q, q.1.2 ∂μ := by
      simpa only [probReal_univ, one_smul] using integral_fun_snd (μ := μ) (ν := μ) (fun q => q.1.2)
    have hezero : (∫ p : (GaussianParent n × GaussianParent n) × ((Fin 2 × Fin 2) × V n), p.2.2
      ∂(μ.prod μ).prod ν) = 0 := by
      calc
        _ = ∫ p : (Fin 2 × Fin 2) × V n, p.2 ∂ν := by
          simpa only [probReal_univ, one_smul] using integral_fun_snd
            (μ := μ.prod μ) (ν := ν) (fun p : (Fin 2 × Fin 2) × V n => p.2)
        _ = ∫ x : V n, x ∂multivariateGaussian 0 E := by
          simpa only [probReal_univ, one_smul] using integral_fun_snd
            (μ := mendelianCoin.prod mendelianCoin) (ν := multivariateGaussian (0 : V n) E) (fun x
              => x)
        _ = 0 := integral_id_multivariateGaussian
    rw [hf0, hf1, hs0, hs1, hezero, add_zero]
    rw [show gaussianBreedingValue = fun q : GaussianParent n => q.1.1 + q.1.2 from rfl,
      integral_add h0 h1]
    module

end Rhone.Statistics.GaussianBreeder
